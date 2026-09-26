"""Accept or retract a maintainer's review of description/declaration correspondence."""

from contextlib import ExitStack
from datetime import datetime, timezone
import json

from django.conf import settings
from django.core.management import call_command
from django.core.management.base import BaseCommand, CommandError

from catalog.content import load_catalog
from catalog.files import staged_json
from catalog.sources import parse_source
from formalization.nodes import formal_signature, load_nodes


def select_nodes(root, nodes, options):
    entry_path, entry_source = None, None
    accepting = options['action'] == 'accept'
    if options['entry']:
        catalog = load_catalog(settings.CORPUS_DIR, root)
        entry = catalog.get(options['entry'])
        if entry is None:
            raise CommandError(f'Unknown entry: {options["entry"]}')
        entry_path = entry['directory'] / 'entry.html'
        entry_source = entry_path.read_bytes()
        blocks, _, _, _ = parse_source(entry_source.decode())
        unplanned = [block['id'] for block in blocks if block['formal_ids'] is None]
        if accepting and unplanned:
            raise CommandError('Entry has blocks without formal mappings: ' + ', '.join(unplanned))
        selected = {node_id for block in blocks for node_id in (block['formal_ids'] or [])}
    else:
        selected = set(options['node'])
    unknown = selected - nodes.keys()
    if unknown:
        raise CommandError('Unknown formal nodes: ' + ', '.join(sorted(unknown)))
    if not selected:
        raise CommandError('No formal nodes selected for review.')
    selected = sorted(selected)
    if accepting:
        missing = [key for key in selected if nodes[key]['declaration'] is None]
        if missing:
            raise CommandError('Declarations missing: ' + ', '.join(missing))
    return selected, entry_path, entry_source


class Command(BaseCommand):
    help = 'Accept or retract review for formal nodes or all nodes linked from a corpus entry.'

    def add_arguments(self, parser):
        action = parser.add_mutually_exclusive_group(required=True)
        action.add_argument('--accept', dest='action', action='store_const', const='accept',
                            help='Approve current descriptions against Lean declarations, refreshing checks if needed.')
        action.add_argument('--retract', dest='action', action='store_const', const='retract',
                            help='Clear recorded approvals without running Lean checks.')
        selection = parser.add_mutually_exclusive_group(required=True)
        selection.add_argument('--node', nargs='+', metavar='ID', help='One or more formal node IDs.')
        selection.add_argument('--entry', metavar='ID',
                               help='Apply the action to all formal nodes linked from this corpus entry.')
        parser.add_argument('--dry-run', action='store_true',
                            help='Preview the selected action without changing node records.')

    def handle(self, **options):
        accepting = options['action'] == 'accept'
        root = settings.REPOSITORY_DIR
        try:
            nodes = load_nodes(root)
            selected, entry_path, entry_source = select_nodes(root, nodes, options)
            paths = {key: root / 'formal/nodes' / f'{key}.json' for key in selected}
            originals = {key: path.read_bytes() for key, path in paths.items()}
            if accepting and any(nodes[key]['target_sha256'] is None for key in selected):
                self.stdout.write('Refreshing Lean verification and review target hashes…')
                call_command('check_formalizations',
                             module=sorted({nodes[key]['module'] for key in selected}),
                             stdout=self.stdout, stderr=self.stderr)

            signature = formal_signature(root)
            nodes = load_nodes(root)
            if any(path.read_bytes() != originals[key] for key, path in paths.items()):
                raise CommandError('Node records changed during review; rerun the command.')
            if accepting:
                if any(nodes[key]['target_sha256'] is None for key in selected):
                    raise CommandError('Current target hashes are unavailable; run check_formalizations.')
                changed = [key for key in selected if not nodes[key]['review_current']]
            else:
                changed = [key for key in selected if nodes[key]['review'] is not None]

            recorded_at = datetime.now(timezone.utc).isoformat()
            with ExitStack() as stack:
                staged = []
                for key in changed:
                    node = json.loads(originals[key])
                    node['review'] = None
                    if accepting:
                        node['review'] = {'sha256': nodes[key]['target_sha256'], 'recorded_at': recorded_at}
                    if not options['dry_run']:
                        temporary = stack.enter_context(staged_json(paths[key], node))
                        staged.append((temporary, paths[key]))

                if (signature != formal_signature(root)
                        or (entry_path is not None and entry_path.read_bytes() != entry_source)):
                    raise CommandError('Review inputs changed; rerun the command.')
                for temporary, destination in staged:
                    temporary.replace(destination)
        except (ValueError, KeyError, OSError) as error:
            raise CommandError(str(error)) from error

        if options['dry_run']:
            verb = f'Would {options["action"]}'
        else:
            verb = 'Accepted' if accepting else 'Retracted'
        self.stdout.write(self.style.SUCCESS(
            f'{verb} review for {len(changed)} node(s); {len(selected) - len(changed)} skipped.'))
        for key in changed:
            detail = f'  {nodes[key]["target_sha256"]}' if accepting else ''
            self.stdout.write(f'  {key}{detail}')
