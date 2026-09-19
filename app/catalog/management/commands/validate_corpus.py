from django.conf import settings
from django.core.management.base import BaseCommand, CommandError

from catalog.content import load_catalog
from catalog.sources import ContentError


class Command(BaseCommand):
    help = "Validate corpus sources, references, assets, reading order, and Lean bindings."

    def handle(self, **options):
        try:
            catalog = load_catalog(settings.CORPUS_DIR,
                                   settings.REPOSITORY_DIR)
        except (ContentError, ValueError, KeyError, OSError) as error:
            raise CommandError(str(error)) from error
        blocks = sum(len(entry["blocks"]) for entry in catalog.values())
        entry_word = 'entry' if len(catalog) == 1 else 'entries'
        self.stdout.write(self.style.SUCCESS(
            f"Validated {len(catalog)} {entry_word} and {blocks} mathematical blocks."))
