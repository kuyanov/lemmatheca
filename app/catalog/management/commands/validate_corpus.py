from pathlib import Path

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.validation import CorpusError, validate_corpus


class Command(BaseCommand):
    help = "Validate corpus structure and references without rendering, building Lean, or writing files."
    requires_system_checks = []

    def add_arguments(self, parser):
        parser.add_argument("--corpus", type=Path, default=settings.CORPUS_DIR,
                            help="Corpus directory (defaults to the configured corpus).")
        parser.add_argument("--check-sources", action="store_true",
                            help="Also check bound Lean source files in the installed environment.")

    def handle(self, *args, **options):
        try:
            entries, nodes, areas = validate_corpus(
                Path(options["corpus"]),
                source_root=settings.REPOSITORY_DIR if options["check_sources"] else None,
            )
        except (CorpusError, OSError) as error:
            raise CommandError(str(error)) from error
        return f"Corpus valid: {entries} entries, {nodes} nodes, {areas} areas."
