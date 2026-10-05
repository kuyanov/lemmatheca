"""Corpus validation stays offline, read-only and linear in records and references."""

from collections import Counter
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.conf import settings
from django.core.management import call_command, CommandError
from django.test import SimpleTestCase

from catalog.files import read_json, write_json
from catalog.validation import CorpusError, acyclic, validate_corpus


class CorpusValidationTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.corpus = self.root / 'corpus'
        (self.corpus / 'nodes').mkdir(parents=True)
        self.taxonomy = self.corpus / 'taxonomy.json'
        self.index = self.corpus / 'area_entries.json'
        write_json(self.taxonomy, {'areas': [
            {'id': 'root', 'title': 'Root', 'parent': None,
                'description': 'Root area.'},
            {'id': 'area', 'title': 'Area', 'parent': 'root',
                'description': 'A child area.'},
        ]})
        write_json(self.index, {'areas': {'area': ['alpha', 'beta']}})
        self.add_entry('alpha', '<a href="beta#fact"></a>')
        self.add_entry('beta', '<a href="alpha#fact"></a>')
        self.node = self.corpus / 'nodes/proof.json'
        write_json(self.node, {'id': 'proof', 'description': 'A planned proof.',
                               'verified': False, 'module': None, 'declaration': None,
                               'dependencies': []})
        self.metadata = self.corpus / 'entries/alpha/entry.json'
        self.source = self.corpus / 'entries/alpha/entry.html'

    def add_entry(self, identifier, body='', formal=None):
        directory = self.corpus / 'entries' / identifier
        directory.mkdir(parents=True)
        write_json(directory / 'entry.json', {
            'id': identifier, 'title': identifier, 'primary_area': 'area',
            'additional_areas': [], 'based_on': [], 'reading_time': 5,
            'summary': 'Summary.', 'abstract': 'Abstract.',
        })
        self.html(directory / 'entry.html', body, formal)

    def html(self, path, body='', formal=None):
        mapping = '' if formal is None else f' data-formal="{formal}"'
        path.write_text(f'<section id="fact" data-kind="lemma"{mapping}>'
                        f'<h2>A fact</h2><p>{body}</p></section>', encoding='utf-8')

    def assert_invalid(self, fragment):
        with self.assertRaisesRegex(CorpusError, fragment):
            validate_corpus(self.corpus)

    def test_optional_statistics_are_checked_for_shape_not_freshness(self):
        path = self.corpus / "statistics.json"
        snapshot = {"entries": 8, "verified_entries": 3, "nodes": 20,
                    "verified_nodes": 12, "contributors": None}
        write_json(path, snapshot)
        validate_corpus(self.corpus)
        for change, message in [({"nodes": "20"}, "nonnegative integer"),
                                ({"contributors": True}, "nonnegative integer"),
                                ({"verified_entries": 9}, "exceed the total")]:
            with self.subTest(change=change):
                write_json(path, {**snapshot, **change})
                self.assert_invalid(message)

    def test_command_is_offline_read_only_and_allows_unbuilt_work(self):
        self.html(self.source, '<a href="beta#fact"></a>', formal='proof')
        before = {path: path.read_bytes()
                  for path in self.corpus.rglob('*') if path.is_file()}
        output = StringIO()
        with patch('subprocess.run', side_effect=AssertionError('No Lean')), \
                patch('catalog.sources.render_block', side_effect=AssertionError('No rendering')), \
                patch('django.template.loader.render_to_string', side_effect=AssertionError('No templates')), \
                patch('catalog.files.records', side_effect=AssertionError('No whole catalog')):
            call_command('validate_corpus', corpus=self.corpus, stdout=output)
        self.assertIn(
            'Corpus valid: 2 entries, 1 nodes, 2 areas.', output.getvalue())
        self.assertEqual(before, {path: path.read_bytes()
                         for path in self.corpus.rglob('*') if path.is_file()})
        # A binding can be planned before its module or declaration has been built.
        node = read_json(self.node)
        write_json(
            self.node, {**node, 'module': 'Lemmatheca.Planned', 'declaration': 'planned'})
        validate_corpus(self.corpus)
        with self.assertRaisesRegex(CorpusError, 'Missing Lean source'):
            validate_corpus(self.corpus, source_root=self.root)
        (self.root / 'formal/Lemmatheca').mkdir(parents=True)
        (self.root / 'formal/Lemmatheca/Planned.lean').write_text('theorem planned : True := by sorry\n')
        validate_corpus(self.corpus, source_root=self.root)

    def test_command_reports_file_and_failure_without_traceback(self):
        self.source.write_text('<section>')
        with self.assertRaisesRegex(CommandError, r'entries/alpha/entry.html: Unclosed'):
            call_command('validate_corpus',
                         corpus=self.corpus, stdout=StringIO())

    def test_metadata_types_ids_and_citations(self):
        original = read_json(self.metadata)
        cases = [
            ({'id': 'wrong'}, 'ID does not match'),
            ({'title': None}, 'title must'),
            ({'reading_time': True}, 'positive integer'),
            ({'reading_time': 0}, 'positive integer'),
            ({'primary_area': []}, 'Invalid primary_area'),
            ({'primary_area': 'missing'}, 'Unknown entry area'),
            ({'additional_areas': ['area']}, 'Primary area'),
            ({'additional_areas': ['root', 'root']}, 'Duplicate'),
            ({'based_on': {}}, 'based_on must'),
            ({'based_on': [None]}, 'Expected an object'),
            ({'based_on': [{'title': 'Book', 'authors': 'Author'}]},
             'authors must'),
            ({'based_on': [{'title': 'Book', 'authors': [
             'Author'], 'doi': 42}]}, 'doi must'),
            ({'based_on': [{'title': 'Book', 'authors': [
             'Author'], 'url': '/book'}]}, 'HTTP'),
            ({'formalization': []}, 'Expected an object'),
            ({'typo': 'value'}, 'Unknown fields'),
        ]
        for update, error in cases:
            with self.subTest(update=update):
                write_json(self.metadata, {**original, **update})
                self.assert_invalid(error)
        write_json(self.metadata, {key: value for key,
                   value in original.items() if key != 'summary'})
        self.assert_invalid('Missing fields: summary')

    def test_generated_summary_may_be_absent_or_stale_but_must_be_well_typed(self):
        record = read_json(self.metadata)
        summary = {'status': 'complete', 'complete': 42, 'total': 42,
                   'unplanned': 0, 'percent': 100, 'label': '100%', 'description': 'Old result'}
        write_json(self.metadata, {**record, 'formalization': summary})
        validate_corpus(self.corpus)
        for update in ({'complete': True}, {'total': 0}, {'percent': 101}, {'status': []}):
            with self.subTest(update=update):
                write_json(self.metadata, {
                           **record, 'formalization': {**summary, **update}})
                with self.assertRaises(CorpusError):
                    validate_corpus(self.corpus)

    def test_invalid_json_and_duplicate_keys(self):
        for content in ('{', '[]', '{"id":"alpha","id":"alpha"}', '{"reading_time":NaN}'):
            with self.subTest(content=content):
                self.metadata.write_text(content)
                with self.assertRaisesRegex(CorpusError, 'entry.json'):
                    validate_corpus(self.corpus)
        self.metadata.write_bytes(b'\xff')
        self.assert_invalid('entry.json')
        self.metadata.write_text('{"id":"alpha","title":"\\ud800","primary_area":"area",'
                                 '"additional_areas":[],"based_on":[],"reading_time":5,'
                                 '"summary":"Summary","abstract":"Abstract"}')
        self.assert_invalid('surrogates not allowed')

    def test_html_structure_and_bindings(self):
        original = self.source.read_text()
        cases = [
            ('', 'at least one block'),
            (original.replace('</section>', ''), 'Unclosed'),
            (original.replace('</p>', '</span>'), 'Unbalanced'),
            ('<p>Outside a block</p>', 'top-level'),
            (original.replace('lemma', 'example'), 'unsupported data-kind'),
            (original.replace('<h2>A fact</h2>', '<h2></h2>'), 'nonempty'),
            (original.replace('<h2>', '<h2 id="lost">'), 'plain text'),
            (original.replace('<h2>A fact</h2>',
             '<h2><a href="#missing">Title</a></h2>'), 'plain text'),
            (original.replace('id="fact"', 'id="fact" id="second"'),
             'Duplicate attributes'),
            (original.replace('<p>', '<p id="fact">'), 'duplicate anchor'),
            (original.replace('<p>', '<p id="fact-title">'), 'Reserved block heading'),
            (original.replace('data-kind="lemma"',
             'data-kind="lemma" data-formal'), 'empty mapping'),
            (original.replace('data-kind="lemma"',
             'data-kind="lemma" data-formal="proof proof"'), 'Duplicate'),
            (original.replace('data-kind="lemma"',
             'data-kind="lemma" data-formal="missing"'), 'Unknown formal nodes'),
            (original.replace('<p>', '<p class>'), 'class needs a value'),
            ('<!DOCTYPE html>' + original, 'document declaration'),
        ]
        for source, error in cases:
            with self.subTest(error=error):
                self.source.write_text(source)
                self.assert_invalid(error)
        self.html(self.source, 'No mathematics.', formal='')
        validate_corpus(self.corpus)
        self.html(self.source, '<span>' * 130 + 'Deep' + '</span>' * 130)
        self.assert_invalid('nesting is too deep')

    def test_references_figures_equations_and_assets(self):
        assets = self.source.parent / 'assets'
        assets.mkdir()
        (assets / 'image.svg').write_text('<svg/>')
        self.html(self.source, r'<span id="local">Local</span><a href="#local">Link</a>'
                  '<figure id="picture"><img src="assets/image.svg" alt="Diagram">'
                  '<figcaption>Caption</figcaption></figure><a href="#picture"></a>'
                  '<table><caption>Table</caption><tr><td>Value</td></tr></table>'
                  r'<div class="math-display">\[x=x\label{eq:one}\]</div>'
                  r'<a href="#eq:one">Equation</a>\eqref{eq:one}')
        validate_corpus(self.corpus)
        cases = [
            ('<a href="missing#fact"></a>', 'Missing referenced entry'),
            ('<a href="beta#missing"></a>', 'mathematical block'),
            ('<a href="#missing"></a>', 'Broken local links'),
            ('<a href="beta#fact?query"></a>', 'mathematical block'),
            ('<a href="beta?query#fact"></a>', 'Broken source link'),
            ('<a href="../beta#fact"></a>', 'Invalid entry reference'),
            ('<a href="http://[bad">Link</a>', 'Invalid'),
            ('<img src="assets/missing.svg" alt="Missing">',
             'Missing or escaped asset'),
            ('<img src="assets/image.svg">', 'Image alt'),
            ('<a href="assets/../entry.json">Download</a>', 'entry-local'),
            ('<figure><img src="assets/image.svg" alt="Diagram"></figure>', 'figcaption'),
            ('<table><caption>One</caption><caption>Two</caption></table>',
             'one direct caption'),
            (r'\eqref{missing}', 'Unknown equation'),
            (r'\label{outside}', 'Equation labels belong'),
            (r'<div class="math-display">\[x\label{a}\label{b}\]</div>',
             'one equation label'),
            (r'<div class="math-display">\[x\tag{2}\label{a}\]</div>',
             'automatically'),
            (r'<span id="a"></span><div class="math-display">\[x\label{a}\]</div>', 'Duplicate anchor'),
            (r'<div class="math-display" id="b">\[x\label{a}\]</div>', 'conflicting'),
        ]
        for body, error in cases:
            with self.subTest(body=body):
                self.html(self.source, body)
                self.assert_invalid(error)
        (assets / 'escape.svg').symlink_to(self.metadata)
        self.html(self.source, '<img src="assets/escape.svg" alt="Escape">')
        self.assert_invalid('escaped asset')

    def test_node_types_missing_hints_and_cycles(self):
        original = read_json(self.node)
        for update, error in [
            ({'id': 'other'}, 'ID does not match'),
            ({'verified': 'false'}, 'boolean'),
            ({'verified': True}, 'unbound'),
            ({'description': []}, 'description must'),
            ({'dependencies': 'proof'}, 'must be a list'),
            ({'dependencies': ['missing']}, 'references missing'),
            ({'dependencies': ['proof']}, 'cycle'),
            ({'dependencies': ['missing', 'missing']}, 'Duplicate'),
            ({'module': 'Lemmatheca'}, 'supplied together'),
            ({'module': '../Lemmatheca', 'declaration': 'proof'}, 'Invalid Lean module'),
            ({'declaration_line': False}, 'positive integer'),
            ({'signature': []}, 'signature must'),
            ({'axioms': ['choice']}, 'Unknown fields: axioms'),
        ]:
            with self.subTest(update=update):
                write_json(self.node, {**original, **update})
                self.assert_invalid(error)
        write_json(self.node, {**original, 'dependencies': ['other']})
        write_json(self.node.with_name('other.json'), {
                   **original, 'id': 'other', 'dependencies': ['proof']})
        self.assert_invalid('cycle')

    def test_area_tree_and_reading_order(self):
        original = read_json(self.taxonomy)
        for areas, error in [
            (original['areas'] * 2, 'Duplicate area'),
            ([{**original['areas'][0], 'parent': 'missing'}], 'references missing'),
            ([{**original['areas'][0], 'parent': 'area'},
             original['areas'][1]], 'cycle'),
            ([{**original['areas'][0], 'parent': 'root'}], 'cycle'),
        ]:
            with self.subTest(error=error):
                write_json(self.taxonomy, {'areas': areas})
                self.assert_invalid(error)
        write_json(self.taxonomy, original)
        for areas, error in [
            ({'missing': []}, 'Unknown area'),
            ({'area': 'alpha'}, 'must be a list'),
            ({'area': ['alpha', 'alpha']}, 'Duplicate'),
            ({'area': ['alpha', 'beta'], 'root': ['alpha']}, 'more than once'),
            ({'area': ['alpha', 'beta', 'missing']}, 'Missing entries'),
            ({'area': ['alpha']}, 'listed once'),
            ({'root': ['alpha', 'beta']}, 'primary area'),
        ]:
            with self.subTest(areas=areas):
                write_json(self.index, {'areas': areas})
                self.assert_invalid(error)

    def test_orphan_entry_directory_and_missing_source(self):
        self.source.unlink()
        self.assert_invalid('entry.html')
        self.html(self.source)
        (self.corpus / 'entries/orphan').mkdir()
        self.assert_invalid('orphan/entry.json')

    def test_each_record_is_read_once_even_with_shared_references(self):
        ids = ['alpha', 'beta']
        for number in range(60):
            identifier = f'entry-{number}'
            ids.append(identifier)
            self.add_entry(
                identifier, '<a href="alpha#fact"></a><a href="beta#fact"></a>' * 10, formal='proof')
        write_json(self.index, {'areas': {'area': ids}})
        reads = Counter()
        original = Path.open

        def opened(path, *args, **kwargs):
            if path.is_relative_to(self.corpus):
                reads[path] += 1
            return original(path, *args, **kwargs)

        with patch.object(Path, 'open', opened):
            self.assertEqual(validate_corpus(self.corpus), (len(ids), 1, 2))
        self.assertEqual(len(reads), 2 * len(ids) + 3)
        self.assertTrue(all(count == 1 for count in reads.values()))

    def test_long_and_shared_dependency_graphs_use_iterative_traversal(self):
        graph = {str(i): [str(i - 1)] if i else []
                 for i in reversed(range(5000))}
        graph['branch'] = list(graph)
        acyclic(graph, 'Hints')
        graph['0'] = ['4999']
        with self.assertRaisesRegex(CorpusError, 'cycle'):
            acyclic(graph, 'Hints')

    def test_source_checks_read_each_shared_module_once_and_reject_bad_encoding(self):
        source = self.root / 'formal/Lemmatheca/Planned.lean'
        source.parent.mkdir(parents=True)
        source.write_text('theorem planned : True := by sorry\n')
        record = {
            **read_json(self.node), 'module': 'Lemmatheca.Planned', 'declaration': 'planned'}
        write_json(self.node, record)
        write_json(self.node.with_name('other.json'),
                   {**record, 'id': 'other'})
        reads = Counter()
        original = Path.open

        def opened(path, *args, **kwargs):
            reads[path] += 1
            return original(path, *args, **kwargs)

        with patch.object(Path, 'open', opened):
            validate_corpus(self.corpus, source_root=self.root)
        self.assertEqual(reads[source], 1)
        source.write_bytes(b'\xff')
        with self.assertRaisesRegex(CorpusError, 'utf-8'):
            validate_corpus(self.corpus, source_root=self.root)

    def test_repository_corpus(self):
        validate_corpus(settings.CORPUS_DIR)
