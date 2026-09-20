"""Source path boundaries used by formal node pages."""

from pathlib import Path
from tempfile import TemporaryDirectory

from django.conf import settings
from django.test import SimpleTestCase

from formalization.lean import lean_source_path
from catalog.sources import ContentError


class LeanSourceTests(SimpleTestCase):
    def test_invalid_paths_and_symlink_escapes_are_rejected(self):
        for source in ('formal/missing.lean', 'formal/lakefile.toml', '../app/config/settings.py',
                       'formal/../private.lean', 'formal/.lake/private.lean',
                       'Mathlib/../private.lean', '/tmp/private.lean', 'formal/dir\\private.lean',
                       'formal//Lemmatheca.lean', 'formal/Lemmatheca.lean/child.lean'):
            with self.subTest(source=source), self.assertRaises(ContentError):
                lean_source_path(source, settings.REPOSITORY_DIR)
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'formal').mkdir()
            (root / 'private.lean').write_text('Do not expose this file')
            (root / 'formal/Escape.lean').symlink_to(root / 'private.lean')
            with self.assertRaises(ContentError):
                lean_source_path('formal/Escape.lean', root)
