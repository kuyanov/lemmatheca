import subprocess

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.proofs import build


class Command(BaseCommand):
    help = "Build Lean and update node verification and entry-list summaries."

    def handle(self, *args, **options):
        try:
            verified, total = build(
                settings.CORPUS_DIR, settings.REPOSITORY_DIR / "formal")
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            raise CommandError(getattr(error, "stdout", None)
                               or str(error)) from error
        return f"Updated {total} nodes: {verified} verified, {total - verified} not verified."
