"""Lean source paths, declaration locations, and verification inputs."""

import re
from pathlib import PurePosixPath

from catalog.files import read_json
from catalog.sources import ContentError


def lean_source_path(source, repository_dir, *, require_file=True):
    parts = source.split('/')
    if (len(parts) < 2 or any(not part or part.startswith('.') for part in parts)
            or '\\' in source or '\x00' in source or PurePosixPath(source).suffix != '.lean'):
        raise ContentError('Invalid Lean source path')
    if parts[0] == 'formal':
        root = repository_dir / 'formal'
    elif parts[0] == 'Mathlib':
        root = repository_dir / 'formal/.lake/packages/mathlib/Mathlib'
    else:
        raise ContentError('Use a formal/ or Mathlib/ source path')
    path = root.joinpath(*parts[1:])
    if not path.resolve().is_relative_to(root.resolve()):
        raise ContentError(f'Lean source is outside its source tree: {source}')
    if path.exists() and not path.is_file():
        raise ContentError(f'Lean source is not a file: {source}')
    if require_file and not path.is_file():
        raise ContentError(f'Missing Lean source: {path}')
    return path


def local_sources(root):
    """Local modules whose changes invalidate formal evidence."""
    paths = set((root / 'formal/Lemmatheca').rglob('*.lean'))
    if (root / 'formal/Lemmatheca.lean').exists():
        paths.add(root / 'formal/Lemmatheca.lean')
    return paths


def code_only(source):
    """Blank nested comments and strings, preserving character and line offsets."""
    result = list(source)
    index, depth, string = 0, 0, False
    while index < len(source):
        pair = source[index:index + 2]
        if not depth and not string and pair == '--':
            end = source.find('\n', index)
            end = len(source) if end < 0 else end
            result[index:end] = ' ' * (end - index)
            index = end
            continue
        if not string and pair == '/-':
            depth += 1
            result[index:index + 2] = '  '
            index += 2
            continue
        if depth and pair == '-/':
            depth -= 1
            result[index:index + 2] = '  '
            index += 2
            continue
        if not depth and source[index] == '"':
            string = not string
            result[index] = ' '
        elif string and source[index] == '\\':
            result[index] = ' '
            if index + 1 < len(source):
                index += 1
                result[index] = '\n' if source[index] == '\n' else ' '
        elif depth or string:
            result[index] = '\n' if source[index] == '\n' else ' '
        index += 1
    return ''.join(result)


def declaration_line(source, declaration):
    """Resolve ordinary namespace-qualified declarations; return None if uncertain."""
    code = code_only(source)
    namespace, scopes = [], []
    pattern = re.compile(
        r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|meta)\s+)*'
        r'(?:(namespace|section|end)\b[ \t]*([\w\'.]+)?|'
        r'(theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom|instance)\s+([\w\'.]+))', re.M)
    for match in pattern.finditer(code):
        scope, scope_name, kind, name = match.groups()
        kind, name = (scope, scope_name) if scope else (kind, name)
        if kind in ('namespace', 'section'):
            scopes.append(len(namespace))
            if kind == 'namespace' and name:
                namespace.extend(name.split('.'))
        elif kind == 'end':
            if scopes:
                del namespace[scopes.pop():]
        elif name:
            full = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join([*namespace, name])
            if full == declaration:
                return code.count('\n', 0, match.start(3)) + 1
    return None


def source_context(source, root, declaration=None):
    path = lean_source_path(source, root, require_file=False)
    text = path.read_text() if path.is_file() else None
    upstream = None
    if source.startswith('Mathlib/'):
        manifest = read_json(root / 'formal/lake-manifest.json')
        commit = next(item['rev'] for item in manifest['packages'] if item['name'] == 'mathlib')
        upstream = f'https://github.com/leanprover-community/mathlib4/blob/{commit}/{source}'
    elif text is None:
        raise ContentError('Local Lean source is missing')
    line = declaration_line(text, declaration) if text is not None and declaration else None
    return {'lean_source': text,
            'source_lines': [{'number': number, 'text': value, 'selected': number == line}
                             for number, value in enumerate(text.splitlines(), 1)] if text is not None else [],
            'declaration_line': line, 'upstream_url': upstream + f'#L{line}' if upstream and line else upstream}


def verification_inputs(root, nodes):
    """Fingerprint local sources and the source imports of all checked modules."""
    from .nodes import ENVIRONMENT
    paths = local_sources(root)
    paths.update(root / 'formal' / name for name in ENVIRONMENT)
    roots = [root / 'formal', *sorted((root / 'formal/.lake/packages').glob('*'))]
    modules = [node['module'] for node in nodes.values() if node['module']]
    visited = set()
    while modules:
        module = modules.pop()
        if module in visited:
            continue
        visited.add(module)
        if module.split('.')[0] in {'Init', 'Lean', 'Std'}:
            continue  # These ship with the pinned Lean toolchain.
        relative = module.replace('.', '/') + '.lean'
        path = next((base / relative for base in roots if (base / relative).is_file()), None)
        if path is None:
            raise ContentError(f'Missing imported Lean source: {module}')
        if not path.resolve().is_relative_to((root / 'formal').resolve()):
            raise ContentError('Imported Lean source is outside formal/')
        paths.add(path)
        code = code_only(path.read_text())
        for match in re.finditer(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', code, re.M):
            imports = match[1].split()
            if imports and imports[0] == 'all':
                imports = imports[1:]
            if any(not re.fullmatch(r"[\w']+(?:\.[\w']+)*", item) for item in imports):
                raise ContentError(f'Cannot fingerprint imports in {module}')
            modules.extend(imports)
    return paths
