"""Lean source paths, declaration locations, and verification inputs."""

import os
import re
from functools import lru_cache
from pathlib import Path, PurePosixPath
from subprocess import SubprocessError, run as run_git

from catalog.files import file_signature, read_json
from catalog.sources import ContentError


TOOLCHAIN_MODULES = ('Init', 'Lean', 'Std')
REVIEW_MODULE = 'Lemmatheca.ReviewChecks'
LIBRARY_INPUT = 'formal/.lake/packages'


def library_packages(root):
    directory = root / LIBRARY_INPUT
    return sorted(path for path in directory.iterdir()
                  if path.is_dir() and not path.name.startswith('.')) if directory.exists() else []


def library_revisions(root):
    """Treat installed Lake packages as immutable checkouts, without scanning sources."""
    pins = {item['name']: item.get('rev') for item in
            read_json(root / 'formal/lake-manifest.json')['packages']}
    revisions = {}
    for package in library_packages(root):
        git = package / '.git'
        if not git.exists():
            # Source archives without Git metadata are trusted to match the lockfile.
            revisions[package.name] = pins.get(package.name)
            continue
        revision = None
        try:
            # Lake normally uses detached HEADs; reading these avoids a subprocess
            # per package. Git handles branches, packed refs, and linked worktrees.
            head = (git / 'HEAD').read_text().strip() if git.is_dir() else ''
            if re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', head):
                revision = head
            else:
                result = run_git(['git', '--no-optional-locks', '-C', str(package),
                                  'rev-parse', '--verify', 'HEAD'],
                                 capture_output=True, text=True, check=True, timeout=5)
                revision = result.stdout.strip()
        except (OSError, SubprocessError):
            # Unreadable revisions invalidate evidence and cannot be checked.
            pass
        revisions[package.name] = revision
    return revisions


def library_overrides(root):
    """Local replacements of library modules still need source-content hashes."""
    def lean_files(directory):
        for base, directories, files in os.walk(directory):
            directories[:] = sorted(
                name for name in directories if not name.startswith('.'))
            for name in files:
                if name.endswith('.lean') or name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                    yield Path(base) / name

    paths = set()
    # Project modules keep their own, per-import-closure fingerprints.
    formal = root / 'formal'
    for directory in formal.iterdir() if formal.exists() else ():
        if directory.is_dir() and not directory.name.startswith('.') and directory.name != 'Lemmatheca':
            paths.update(lean_files(directory))
    namespaces = {path.stem for package in library_packages(root) for path in package.iterdir()
                  if not path.name.startswith('.') and (path.is_dir() or path.suffix == '.lean')}
    paths.update(
        formal / f'{name}.lean' for name in namespaces if (formal / f'{name}.lean').is_file())
    return paths


def pinned_lean_version(root):
    toolchain = (root / 'formal/lean-toolchain').read_text().strip()
    match = re.fullmatch(
        r'leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+(?:-[\w.-]+)?)', toolchain)
    if not match:
        raise ContentError(
            'Lean source navigation requires a versioned leanprover/lean4 toolchain')
    return match[1]


def lean_source_path(source, repository_dir, *, require_file=True):
    parts = source.split('/')
    if (len(parts) < 2 or any(not part or part.startswith('.') for part in parts)
            or '\\' in source or '\x00' in source or PurePosixPath(source).suffix != '.lean'):
        raise ContentError('Invalid Lean source path')
    if parts[0] == 'formal':
        root = repository_dir / 'formal'
    elif parts[0] == 'Mathlib':
        root = repository_dir / 'formal/.lake/packages/mathlib/Mathlib'
    elif parts[0] in TOOLCHAIN_MODULES:
        version = pinned_lean_version(repository_dir)
        elan = Path(os.environ.get(
            'ELAN_HOME', Path.home() / '.elan')).expanduser()
        root = elan / 'toolchains' / \
            f'leanprover--lean4---{version}' / 'src/lean' / parts[0]
    else:
        raise ContentError(
            'Use a formal/, Mathlib/, Init/, Lean/, or Std/ source path')
    path = root.joinpath(*parts[1:])
    if not path.resolve().is_relative_to(root.resolve()):
        raise ContentError(f'Lean source is outside its source tree: {source}')
    if path.exists() and not path.is_file():
        raise ContentError(f'Lean source is not a file: {source}')
    if require_file and not path.is_file():
        raise ContentError(f'Missing Lean source: {path}')
    return path


def local_sources(root):
    """Local modules watched for changes by the reader's catalog cache."""
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
            full = name.removeprefix('_root_.') if name.startswith(
                '_root_.') else '.'.join([*namespace, name])
            if full == declaration:
                return code.count('\n', 0, match.start(3)) + 1
    return None


def source_context(source, root, declaration=None, *, checked_line=None):
    path = lean_source_path(source, root, require_file=False)
    text = path.read_text() if path.is_file() else None
    upstream = None
    upstream_name = None
    if source.startswith('Mathlib/'):
        manifest = read_json(root / 'formal/lake-manifest.json')
        commit = next(item['rev'] for item in manifest['packages']
                      if item['name'] == 'mathlib')
        upstream = f'https://github.com/leanprover-community/mathlib4/blob/{commit}/{source}'
        upstream_name = 'mathlib'
    elif source.split('/')[0] in TOOLCHAIN_MODULES:
        version = pinned_lean_version(root)
        upstream = f'https://github.com/leanprover/lean4/blob/{version}/src/{source}'
        upstream_name = 'Lean'
    elif text is None:
        upstream_name = 'local Lean'
    # Current checker evidence includes Lean's locations for anonymous instances
    # and other generated names that cannot be found by scanning source text.
    line = checked_line if type(
        checked_line) is int and checked_line > 0 else None
    if text is not None and line is not None and line > len(text.splitlines()):
        line = None
    if line is None and text is not None and declaration:
        line = declaration_line(text, declaration)
    return {'lean_source': text,
            'source_lines': [{'number': number, 'text': value, 'selected': number == line}
                             for number, value in enumerate(text.splitlines(), 1)] if text is not None else [],
            'declaration_line': line, 'upstream_name': upstream_name,
            'upstream_url': upstream + f'#L{line}' if upstream and line else upstream}


def source_roots(root):
    return [root / 'formal', *sorted((root / 'formal/.lake/packages').glob('*'))]


def module_source_path(module, root, *, roots=None, required=True):
    if not re.fullmatch(r"[\w']+(?:\.[\w']+)*", module):
        raise ContentError(f'Invalid imported Lean module: {module}')
    relative = module.replace('.', '/') + '.lean'
    path = next((base / relative for base in (roots if roots is not None else source_roots(root))
                 if (base / relative).is_file()), None)
    if path is None:
        if required:
            raise ContentError(f'Missing imported Lean source: {module}')
        return None
    if not path.resolve().is_relative_to((root / 'formal').resolve()):
        raise ContentError('Imported Lean source is outside formal/')
    return path


@lru_cache(maxsize=8192)
def _source_imports(path, signature):
    imports = []
    for match in re.finditer(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',
                             code_only(path.read_text()), re.M):
        names = match[1].split()
        if names and names[0] == 'all':
            names = names[1:]
        if any(not re.fullmatch(r"[\w']+(?:\.[\w']+)*", name) for name in names):
            raise ContentError(f'Cannot fingerprint imports in {path}')
        imports.extend(names)
    return tuple(imports)


def verification_inputs(root, module):
    """Local import closure and environment, with one shared library fingerprint."""
    from .nodes import ENVIRONMENT
    paths = {root / 'formal' / name for name in ENVIRONMENT}
    roots = source_roots(root)
    modules = [module, REVIEW_MODULE]
    visited = set()
    while modules:
        module = modules.pop()
        if module in visited:
            continue
        visited.add(module)
        if module.split('.')[0] in TOOLCHAIN_MODULES:
            continue  # These ship with the pinned Lean toolchain.
        path = module_source_path(module, root, roots=roots)
        paths.add(
            root / LIBRARY_INPUT if path.is_relative_to(root / LIBRARY_INPUT) else path)
        modules.extend(_source_imports(path, file_signature(path)))
    return paths
