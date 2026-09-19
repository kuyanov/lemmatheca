"""Build an isolated corpus with archived examples for reader regression tests."""

import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory

from django.conf import settings
from django.test import override_settings


def copy_test_corpus(destination):
    source = settings.CORPUS_DIR
    shutil.copytree(source / 'entries', destination / 'entries')
    for entry in (source / 'backup').iterdir():
        if entry.is_dir():
            shutil.copytree(entry, destination / 'entries' / entry.name)
    shutil.copyfile(source / 'taxonomy_complete.json',
                    destination / 'taxonomy.json')
    order = {}
    for path in sorted((destination / 'entries').glob('*/entry.json')):
        entry = json.loads(path.read_text())
        order.setdefault(entry['primary_area'], []).append(entry['id'])
    (destination / 'reading-order.json').write_text(
        json.dumps({'format_version': 1, 'areas': order}))


class ExampleCorpusMixin:
    def setUp(self):
        super().setUp()
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.corpus = Path(temporary.name) / 'corpus'
        copy_test_corpus(self.corpus)
        configured = override_settings(
            CORPUS_DIR=self.corpus,
            STATICFILES_DIRS=[settings.BASE_DIR / 'static', *[
                (f'entries/{path.parent.name}', path)
                for path in (self.corpus / 'entries').glob('*/assets')]],
        )
        configured.enable()
        self.addCleanup(configured.disable)
