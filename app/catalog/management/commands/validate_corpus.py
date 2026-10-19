from pathlib import Path

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.corpus_index import configured_index_path, write_index
from catalog.validation import validate_corpus


class Command(BaseCommand):
    help = ("Validate corpus structure and references without rendering or Lean. "
            "Read-only unless --write-index exports a derived cache.")
    requires_system_checks = []

    def add_arguments(self, parser):
        parser.add_argument("--check-sources", action="store_true",
                            help="Also check bound Lean source files in the installed environment.")
        parser.add_argument("--write-index", nargs="?", type=Path, metavar="PATH",
                            const=configured_index_path(),
                            help="Export a derived index after validation (default: configured index path or repository artifacts/corpus-index.json).")

    def handle(self, *args, **options):
        try:
            source_root = settings.REPOSITORY_DIR if options["check_sources"] else None
            if options["write_index"] is None:
                entries, nodes, areas = validate_corpus(settings.CORPUS_DIR, source_root=source_root)
            else:
                destination = Path(options["write_index"])
                document = write_index(settings.CORPUS_DIR, destination, source_root=source_root)
                counts = document["counts"]
                entries, nodes, areas = counts["entries"], counts["nodes"], counts["areas"]
                self.stdout.write(f"Wrote corpus index: {destination} ({document['revision']}).")
        except (OSError, ValueError) as error:
            raise CommandError(str(error)) from error
        return f"Corpus valid: {entries} entries, {nodes} nodes, {areas} areas."
