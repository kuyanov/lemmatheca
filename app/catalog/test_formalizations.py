"""Keep type-checked sorry statements out of the complete-proof report."""

from io import StringIO
import json
from pathlib import Path
import shutil
from subprocess import CompletedProcess
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.core.management import call_command
from django.core.management.base import CommandError
from django.test import SimpleTestCase, override_settings

from .metadata import formal_source_path


class FormalizationCommandTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.corpus = self.root / 'corpus'
        shutil.copytree(settings.CORPUS_DIR, self.corpus)
        self.complete = set()
        self.pending = set()
        paths = {settings.REPOSITORY_DIR / 'formal' / name for name in
                 ('Lemmatheca.lean', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain')}
        for path in (self.corpus / 'entries').glob('*/entry.json'):
            for block in json.loads(path.read_text())['blocks'].values():
                formal = block['formalization']
                if formal['status'] == 'complete':
                    self.complete.add(formal['declaration'])
                    paths.add(formal_source_path(formal, settings.REPOSITORY_DIR))
                for dependency in formal['unformalized_dependencies']:
                    self.pending.add(dependency['declaration'])
                    paths.add(formal_source_path(dependency, settings.REPOSITORY_DIR))
        for path in paths:
            target = self.root / path.relative_to(settings.REPOSITORY_DIR)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
        self.report = self.root / 'formal/checks/sumsets.json'

    def run_check(self, contaminated=None):
        # Simulate Lean's transitive axiom reports; real compilation is checked
        # separately by the management command against the pinned environment.
        output = '\n'.join(
            f"'{name}' depends on axioms: [propext, "
            + ('sorryAx' if name in self.pending or name == contaminated else 'Quot.sound') + ']'
            for name in self.complete | self.pending)
        result = CompletedProcess([], 0, stdout=output, stderr='')
        with override_settings(REPOSITORY_DIR=self.root, CORPUS_DIR=self.corpus), patch(
                'catalog.management.commands.check_formalizations.subprocess.run', return_value=result):
            call_command('check_formalizations', stdout=StringIO())

    def test_pending_statements_are_reported_separately_from_complete_proofs(self):
        self.run_check()
        report = json.loads(self.report.read_text())
        self.assertEqual({item['name'] for item in report['declarations']}, self.complete)
        self.assertEqual({item['name'] for item in report['pending_dependencies']}, self.pending)
        self.assertTrue(all('sorryAx' in item['axioms'] for item in report['pending_dependencies']))
        self.assertTrue(all('sorryAx' not in item['axioms'] for item in report['declarations']))

    def test_complete_proof_using_sorry_even_transitively_cannot_pass(self):
        with self.assertRaisesRegex(CommandError, 'unapproved axioms.*sorryAx'):
            self.run_check(contaminated='Lemmatheca.triple_sumset_card_lower_bound')
        self.assertFalse(self.report.exists())
