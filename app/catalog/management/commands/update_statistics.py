import subprocess

from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.files import write_json
from catalog.statistics import prepare_statistics, read_statistics
from catalog.validation import validate_statistics


class Command(BaseCommand):
    help = "Refresh home-page statistics from saved corpus metadata and Git authors, without Lean."

    def handle(self, *args, **options):
        try:
            statistics = prepare_statistics(settings.CORPUS_DIR, settings.REPOSITORY_DIR)
            validate_statistics(statistics)
            if statistics == read_statistics(settings.CORPUS_DIR):
                return "Statistics unchanged."
            write_json(settings.CORPUS_DIR / "statistics.json", statistics)
        except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
            raise CommandError(str(error)) from error
        return "Updated home-page statistics."
