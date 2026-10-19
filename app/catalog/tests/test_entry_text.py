"""On-demand prose extraction and bounded cache freshness/accounting."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from django.test import SimpleTestCase, override_settings

from catalog import entry_text
from catalog.entry_text import (
    LRUEntryTextCache, clear_text_cache, get_entry_text, render_text, text_cache_info,
)
from catalog.sources import Element
from catalog.validation import CorpusError, checked_source


class EntryTextTests(SimpleTestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.corpus = Path(temporary.name)
        self.addCleanup(clear_text_cache)

    def source(self, entry_id="alpha", text="Visible words."):
        path = self.corpus / "entries" / entry_id / "entry.html"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f'''<section id="fact" data-kind="lemma" data-formal="proof">
            <h2>A fact</h2><p>{text}</p>
            </section>''', encoding="utf-8")
        return path

    def test_extracts_text_answers_and_all_links_in_source_order(self):
        path = self.source()
        path.write_text(r'''<section id="question" data-kind="question" data-formal="">
            <h2>A question</h2><p>First paragraph with
            \(x=x\).</p><p>Second <em>paragraph</em>.</p>
            <ul><li>First item</li><li>Second item</li></ul>
            <a href="beta#fact"></a><a href="https://example.com/">Source</a>
            <a href="assets/data.txt">Data</a><a href="#local">Nearby</a>
            <span id="local">An anchor.</span>
            <script>ignored script</script><style>ignored style</style>
            <details class="question-answer"><summary>Show answer</summary>
                <p>The hidden answer.</p><a href="beta#fact">Earlier fact</a>
            </details>
            </section><section id="planned" data-kind="lemma">
            <h2>Later</h2><p>Still unplanned.</p></section>''', encoding="utf-8")
        with patch("catalog.sources.render_block", side_effect=AssertionError("No rendering")), \
                patch("subprocess.run", side_effect=AssertionError("No Lean")):
            result = LRUEntryTextCache().get(self.corpus, "alpha")
        self.assertEqual(list(result), ["question", "planned"])
        block = result["question"]
        self.assertEqual(block["title"], "A question")
        self.assertEqual(block["kind"], "question")
        self.assertEqual(block["formal_ids"], [])
        self.assertIsNone(result["planned"]["formal_ids"])
        text = render_text(block["text"])
        self.assertIn("First paragraph with \\(x=x\\).\nSecond paragraph.", text)
        self.assertIn("First item\nSecond item", text)
        self.assertNotIn("hidden answer", text)
        self.assertNotIn("ignored", text)
        self.assertIn("Resolved fact", render_text(block["text"], {0: "Resolved fact"}))
        self.assertEqual(block["answer_text"], "The hidden answer.\nEarlier fact")
        self.assertEqual([link["kind"] for link in block["links"]],
                         ["internal", "external", "asset", "internal", "internal"])
        self.assertEqual(block["links"][0]["target"], "beta#fact")
        self.assertEqual(block["links"][0]["text"], "")
        self.assertEqual(block["links"][3]["target"], "alpha#local")
        self.assertTrue(block["links"][-1]["in_answer"])
        self.assertTrue(all(not link["in_answer"] for link in block["links"][:-1]))

        def check_plain(value):
            self.assertNotIsInstance(value, Element)
            self.assertIsInstance(value, (dict, list, str, int, bool, type(None)))
            children = value.values() if isinstance(value, dict) else value if isinstance(value, list) else []
            for child in children:
                check_plain(child)

        check_plain(result)

    def test_cache_reuses_parse_and_invalidates_in_place_edits(self):
        self.source()
        cache = LRUEntryTextCache()
        with patch("catalog.entry_text.checked_source", wraps=checked_source) as parser:
            first = cache.get(self.corpus, "alpha")
            self.assertIs(cache.get(self.corpus, "alpha"), first)
            self.assertEqual(parser.call_count, 1)
            self.source(text="Different words with a new length.")
            updated = cache.get(self.corpus, "alpha")
            self.assertEqual(parser.call_count, 2)
            self.assertIsNot(updated, first)
            self.assertEqual(updated["fact"]["text"], "Different words with a new length.")
        self.assertEqual(cache.info()["entries"], 1)

    def test_atomic_replacement_invalidates_same_size_and_timestamp(self):
        import os

        path = self.source(text="Old words.")
        cache = LRUEntryTextCache()
        first = cache.get(self.corpus, "alpha")
        previous = path.stat()
        replacement = path.with_name("replacement.html")
        replacement.write_text(path.read_text().replace("Old words.", "New words."))
        os.utime(replacement, ns=(previous.st_atime_ns, previous.st_mtime_ns))
        replacement.replace(path)
        updated = cache.get(self.corpus, "alpha")
        self.assertIsNot(first, updated)
        self.assertEqual(updated["fact"]["text"], "New words.")
        self.assertEqual(cache.info()["entries"], 1)

    def test_lru_entry_count_and_byte_budget_evict_oldest(self):
        for entry in ("alpha", "beta", "gamma"):
            self.source(entry)
        cache = LRUEntryTextCache(max_entries=2)
        with patch("catalog.entry_text.checked_source", wraps=checked_source) as parser:
            first = cache.get(self.corpus, "alpha")
            cache.get(self.corpus, "beta")
            self.assertIs(cache.get(self.corpus, "alpha"), first)
            cache.get(self.corpus, "gamma")
            self.assertEqual(cache.info()["entries"], 2)
            self.assertEqual(cache.info()["evictions"], 1)
            self.assertIs(cache.get(self.corpus, "alpha"), first)
            cache.get(self.corpus, "beta")
            self.assertEqual(parser.call_count, 4)
        probe = LRUEntryTextCache()
        probe.get(self.corpus, "alpha")
        one_entry = probe.info()["bytes"]
        self.assertGreater(one_entry, self.corpus.joinpath("entries/alpha/entry.html").stat().st_size)
        cache = LRUEntryTextCache(max_bytes=one_entry + 128)
        cache.get(self.corpus, "alpha")
        cache.get(self.corpus, "beta")
        self.assertEqual(cache.info()["entries"], 1)
        self.assertLessEqual(cache.info()["bytes"], cache.info()["max_bytes"])
        self.assertEqual(cache.info()["evictions"], 1)

    def test_oversized_or_disabled_cache_still_returns_text(self):
        self.source()
        for options in ({"max_bytes": 1}, {"max_bytes": 0}, {"max_entries": 0}):
            with self.subTest(options=options):
                cache = LRUEntryTextCache(**options)
                with patch("catalog.entry_text.checked_source", wraps=checked_source) as parser:
                    self.assertEqual(cache.get(self.corpus, "alpha")["fact"]["text"], "Visible words.")
                    cache.get(self.corpus, "alpha")
                    self.assertEqual(parser.call_count, 2)
                self.assertEqual(cache.info()["bytes"], 0)
                self.assertEqual(cache.info()["entries"], 0)

    def test_malformed_and_deleted_sources_remove_stale_cache(self):
        path = self.source()
        cache = LRUEntryTextCache()
        cache.get(self.corpus, "alpha")
        path.write_text("<section>")
        with self.assertRaises(CorpusError):
            cache.get(self.corpus, "alpha")
        self.assertEqual(cache.info()["entries"], 0)
        self.source()
        cache.get(self.corpus, "alpha")
        path.unlink()
        with self.assertRaises(FileNotFoundError):
            cache.get(self.corpus, "alpha")
        self.assertEqual(cache.info()["bytes"], 0)

    def test_changes_during_parse_retry_without_caching_old_version(self):
        self.source()
        cache = LRUEntryTextCache()
        original = entry_text._parse_entry_text
        calls = 0

        def changing_parse(source, entry_id):
            nonlocal calls
            result = original(source, entry_id)
            calls += 1
            if calls == 1:
                self.source(text="Updated during parsing.")
            return result

        with patch("catalog.entry_text._parse_entry_text", side_effect=changing_parse):
            result = cache.get(self.corpus, "alpha")
        self.assertEqual(calls, 2)
        self.assertEqual(result["fact"]["text"], "Updated during parsing.")
        self.assertEqual(cache.info()["entries"], 1)

    def test_continuously_changing_source_stops_retrying(self):
        self.source()
        cache = LRUEntryTextCache()
        original = entry_text._parse_entry_text
        calls = 0

        def changing_parse(source, entry_id):
            nonlocal calls
            result = original(source, entry_id)
            calls += 1
            # The first replacement must differ in size from "Visible words."
            # too: a filesystem may report identical timestamps within a tick.
            self.source(text="Changed " + "again " * (calls + 1))
            return result

        with patch("catalog.entry_text._identity",
                   side_effect=lambda stat: (stat.st_dev, stat.st_ino, stat.st_size, 0, 0)), \
                patch("catalog.entry_text._parse_entry_text", side_effect=changing_parse):
            with self.assertRaisesMessage(OSError, "changed repeatedly"):
                cache.get(self.corpus, "alpha")
        self.assertEqual(calls, 3)
        self.assertEqual(cache.info()["entries"], 0)

    def test_rejects_invalid_identifiers_before_filesystem_access(self):
        cache = LRUEntryTextCache()
        with patch.object(Path, "resolve", side_effect=AssertionError("No path access")):
            for value in ("../alpha", "alpha/beta", "alpha.html", "", None):
                with self.subTest(value=value), self.assertRaises(FileNotFoundError):
                    cache.get(self.corpus, value)

    def test_runtime_settings_prune_existing_singleton_cache(self):
        self.source()
        with override_settings(CORPUS_TEXT_CACHE_BYTES=100_000, CORPUS_TEXT_CACHE_ENTRIES=2):
            get_entry_text(self.corpus, "alpha")
            self.assertEqual(text_cache_info()["entries"], 1)
        with override_settings(CORPUS_TEXT_CACHE_BYTES=0):
            get_entry_text(self.corpus, "alpha")
            self.assertEqual(text_cache_info()["entries"], 0)
            self.assertEqual(text_cache_info()["bytes"], 0)

    def test_concurrent_calls_parse_once_and_keep_consistent_accounting(self):
        self.source()
        cache = LRUEntryTextCache()
        with patch("catalog.entry_text.checked_source", wraps=checked_source) as parser:
            with ThreadPoolExecutor(max_workers=8) as pool:
                results = list(pool.map(lambda _: cache.get(self.corpus, "alpha"), range(16)))
            self.assertEqual(parser.call_count, 1)
        self.assertTrue(all(result is results[0] for result in results))
        self.assertEqual(cache.info()["entries"], 1)
        self.assertEqual(cache.info()["hits"], 15)
        self.assertLessEqual(cache.info()["bytes"], cache.info()["max_bytes"])

    def test_invalid_limits_are_rejected_without_discarding_cache(self):
        self.source()
        cache = LRUEntryTextCache()
        first = cache.get(self.corpus, "alpha")
        for value in (-1, True, "1024"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                cache.configure(max_bytes=value, max_entries=128)
        self.assertIs(cache.get(self.corpus, "alpha"), first)
