from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.authoring_records import write_authoring_indexes


class Command(BaseCommand):
    help = "Rebuild the compact source-review and reference-planning navigation catalogs."
    requires_system_checks = []

    def handle(self, *args, **options):
        try:
            sources, planning = write_authoring_indexes(settings.CORPUS_DIR)
        except (OSError, ValueError, TypeError) as error:
            raise CommandError(str(error)) from error
        return (f"Indexed {len(sources['sources'])} sources, {len(sources['findings'])} findings, "
                f"and {len(planning['records'])} planning records.")
