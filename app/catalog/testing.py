"""Small, isolated corpus shared by reader and formalization tests."""

import json
from pathlib import Path
from tempfile import TemporaryDirectory

from django.conf import settings
from django.test import override_settings


FIRST_SOURCE = r'''
<section id="sets" data-kind="definition">
  <h2>Sets</h2><p>Some sets \(A\) and \(B\).</p>
  <table><caption>Notation</caption><tr><th scope="col">Sum</th></tr>
    <tr><td>\(a+b\)</td></tr></table>
  <figure id="diagram"><img src="assets/diagram.svg" alt="Two sets">
    <figcaption>A picture.</figcaption></figure>
</section>
<section id="equality" data-kind="definition"><h2>Equality</h2><p>Equal sets.</p></section>
<section id="bound" data-kind="lemma">
  <h2>A basic bound</h2>
  <p>Use <a href="#sets">Sets</a> and <a href="#diagram">Figure</a>.
    See \eqref{eq:bound}, \(\eqref{eq:bound}\), and \(1+\eqref{eq:bound}\).</p>
  <div class="math-display">\[1 \le 2.\label{eq:bound}\]</div>
</section>
<section id="question" data-kind="question">
  <h2>Why?</h2><details class="question-answer"><summary>Answer</summary>
    <p>See <a href="../second/entry.html#result">Another result</a>.</p>
  </details>
</section>
'''
SECOND_SOURCE = '''
<section id="result" data-kind="theorem"><h2>Another result</h2>
  <p>Use <a href="../first/entry.html#bound">A basic bound</a>.</p>
</section>
'''


class CorpusFixtureMixin:
    entry_sources = {'first': FIRST_SOURCE, 'second': SECOND_SOURCE}

    def setUp(self):
        super().setUp()
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.corpus = self.root / 'corpus'
        self.corpus.mkdir()
        (self.corpus / 'taxonomy.json').write_text(json.dumps({'areas': [
            {'id': 'math', 'title': 'Mathematics',
                'parent': None, 'description': 'Mathematics.'},
            {'id': 'sets', 'title': 'Sets', 'parent': 'math',
                'description': 'Sets and maps.'},
        ]}))
        for entry_id, source in self.entry_sources.items():
            self.write_entry(entry_id, source)
        (self.corpus / 'reading-order.json').write_text(json.dumps(
            {'format_version': 1, 'areas': {'sets': list(self.entry_sources)}}))
        assets = self.corpus / 'entries/first/assets'
        assets.mkdir()
        (assets / 'diagram.svg').write_text('<svg xmlns="http://www.w3.org/2000/svg"/>')
        configured = override_settings(
            REPOSITORY_DIR=self.root, CORPUS_DIR=self.corpus,
            STATICFILES_DIRS=[settings.BASE_DIR /
                              'static', ('entries/first', assets)],
        )
        configured.enable()
        self.addCleanup(configured.disable)

    def write_entry(self, entry_id, source):
        directory = self.corpus / 'entries' / entry_id
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'entry.json').write_text(json.dumps({
            'id': entry_id, 'title': f'Entry {entry_id}', 'based_on': [],
            'primary_area': 'sets', 'additional_areas': [], 'status': 'draft',
            'reading_time': 1, 'summary': 'A short example.', 'abstract': 'Some mathematics.',
        }))
        (directory / 'entry.html').write_text(source)
