import subprocess

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.corpus_index import configured_index_path, write_index
from catalog.proofs import build


class Command(BaseCommand):
    help = "Build Lean, update proof metadata, and refresh the corpus index."

    def handle(self, *args, **options):
        try:
            verified, total = build(
                settings.CORPUS_DIR, settings.REPOSITORY_DIR / "formal")
            index_path = configured_index_path()
            write_index(settings.CORPUS_DIR, index_path)
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            raise CommandError(getattr(error, "stdout", None)
                               or str(error)) from error
        self.stdout.write(f"Corpus index written: {index_path}")
        return f"Updated {total} nodes: {verified} verified, {total - verified} not verified."
