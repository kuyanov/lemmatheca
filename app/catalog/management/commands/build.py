import subprocess
from pathlib import Path

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.build import build_corpus
from catalog.corpus_index import configured_index_path


class Command(BaseCommand):
    help = "Validate the corpus and rebuild proof metadata, summaries and indexes."
    requires_system_checks = []

    def add_arguments(self, parser):
        parser.epilog = (
            "Default: run Lean and save generated data. Use --check to compare "
            "without publishing, or --no-lean --check for structural validation "
            "only. See docs/build.md for stages, outputs and examples.")
        parser.add_argument("--no-lean", action="store_true",
                            help="Skip Lean and reuse saved proof results; with --check, validate authored inputs only.")
        parser.add_argument("--check", action="store_true",
                            help="Publish nothing; with Lean, fail if saved proof metadata, summaries, catalogs or index differ from regeneration.")
        parser.add_argument("--check-sources", action="store_true",
                            help="Also require readable installed .lean sources for bound modules; does not invoke Lean itself.")
        parser.add_argument("--index", type=Path, metavar="PATH",
                            help="Index output or full-check comparison path (default: DJANGO_CORPUS_INDEX_PATH or corpus/index.json).")

    def handle(self, *args, **options):
        try:
            result = build_corpus(
                settings.CORPUS_DIR, settings.REPOSITORY_DIR / "formal",
                options["index"] or configured_index_path(),
                no_lean=options["no_lean"], check=options["check"],
                check_sources=options["check_sources"])
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            raise CommandError(getattr(error, "stdout", None)
                               or str(error)) from error
        counts = result["counts"]
        for warning in result["warnings"]:
            self.stderr.write(self.style.WARNING(f"WARNING: {warning}"))
        self.stdout.write(f"Corpus valid: {counts['entries']} entries, {counts['nodes']} nodes, {counts['areas']} areas.")
        if options["check"]:
            return ("Generated corpus data is current; Lean verification checked."
                    if result["lean_checked"] else "Read-only check complete; Lean verification not rerun.")
        self.stdout.write(f"Corpus index written: {result['index_path']}")
        verification = "checked" if result["lean_checked"] else "reused, not rerun"
        return f"Lean verification {verification}: {result['verified']} of {counts['nodes']} nodes verified."
