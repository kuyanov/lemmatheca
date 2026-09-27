"""Source path boundaries used by formal node pages."""

import os
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.test import SimpleTestCase

from formalization.lean import lean_source_path
from catalog.sources import ContentError


class LeanSourceTests(SimpleTestCase):
    def test_invalid_paths_and_symlink_escapes_are_rejected(self):
        for source in ('formal/missing.lean', 'formal/lakefile.toml', '../app/config/settings.py',
                       'formal/../private.lean', 'formal/.lake/private.lean',
                       'Init/../private.lean', 'Lean/.private.lean', 'Std//private.lean',
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

    def test_toolchain_source_symlinks_cannot_escape_the_source_tree(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'formal').mkdir()
            (root / 'formal/lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
            (root / 'private.lean').write_text('Do not expose this file')
            elan = root / 'elan'
            source = elan / 'toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Escape.lean'
            source.parent.mkdir(parents=True)
            source.symlink_to(root / 'private.lean')
            with patch.dict(os.environ, {'ELAN_HOME': str(elan)}), self.assertRaises(ContentError):
                lean_source_path('Init/Escape.lean', root)
