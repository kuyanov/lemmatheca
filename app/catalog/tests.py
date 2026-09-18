from html.parser import HTMLParser
from urllib.parse import urljoin, urlsplit
from unittest.mock import patch

from django.contrib.staticfiles import finders
from django.conf import settings
from django.template.base import Lexer, TokenType
from django.template.loader import get_template
from django.test import SimpleTestCase, override_settings
from django.urls import reverse

from .content import ancestors, area_link, areas, children, entries, example_entry, next_entry


class LinkParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []
        self.anchors = []
        self.ids = []
        self.details = []
        self.current_anchor = None

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.append(attrs["id"])
        if tag == "details":
            self.details.append(attrs)
        if tag == "a":
            self.links.append(attrs["href"])
            self.current_anchor = {**attrs, "text": ""}
            self.anchors.append(self.current_anchor)

    def handle_data(self, data):
        if self.current_anchor is not None:
            self.current_anchor["text"] += data

    def handle_endtag(self, tag):
        if tag == "a":
            self.current_anchor = None


class CatalogTests(SimpleTestCase):
    def test_formatter_has_not_split_django_template_tags(self):
        template_dir = settings.BASE_DIR / "templates"
        for path in template_dir.rglob("*.html"):
            with self.subTest(template=path.relative_to(template_dir)):
                # Split tags can silently become literal text, even when the
                # template still compiles. Check Django's tokenization as well.
                for token in Lexer(path.read_text()).tokenize():
                    if token.token_type == TokenType.TEXT:
                        self.assertNotRegex(
                            token.contents, r"\{[%{]", "Unrecognized Django template tag")
                get_template(str(path.relative_to(template_dir)))

    def test_complete_taxonomy_is_reachable(self):
        roots = children()
        self.assertEqual(len(roots), 12)
        for root in roots:
            self.assertTrue(children(root["id"]), root["title"])
        for area in areas().values():
            with self.subTest(area=area["id"]):
                response = self.client.get(area_link(area)["url"])
                self.assertEqual(response.status_code, 200)
                for ancestor in ancestors(area):
                    self.assertContains(response, ancestor["title"])

    def test_all_rendered_navigation_links_resolve(self):
        urls = [reverse("catalog:home"), *(area_link(area)["url"]
                                           for area in areas().values())]
        urls.extend(reverse("catalog:entry", args=[entry["id"]])
                    for entry in entries().values())
        for url in urls:
            parser = LinkParser()
            parser.feed(self.client.get(url).content.decode())
            for link in parser.links:
                if link.startswith(("/", "#")):
                    with self.subTest(source=url, target=link):
                        target = urlsplit(urljoin(url, link))
                        response = self.client.get(
                            target.path + ("?" + target.query if target.query else ""))
                        self.assertEqual(response.status_code, 200)
                        if target.fragment:
                            destination = LinkParser()
                            destination.feed(response.content.decode())
                            self.assertIn(target.fragment, destination.ids)

    def test_articles_contain_locally_numbered_mathematical_blocks(self):
        response = self.client.get(area_link(areas()["sumsets"])["url"])
        self.assertContains(response, "2 entries")
        for entry in entries().values():
            with self.subTest(entry=entry["id"]):
                url = reverse("catalog:entry", args=[entry["id"]])
                self.assertEqual(url, f"/entries/{entry['id']}/")
                self.assertContains(response, url)
                self.assertContains(response, entry["title"])
                article = self.client.get(url)
                for label in ["Definition 1", "Lemma 1", "Theorem 1", "Question 1"]:
                    self.assertContains(article, label)
                self.assertContains(article, "awaiting maintainer review")
                self.assertContains(article, "katex.min.js")
                parser = LinkParser()
                parser.feed(article.content.decode())
                self.assertEqual(len(parser.ids), len(set(parser.ids)))
                for block in entry["blocks"]:
                    self.assertIn(block["id"], parser.ids)
                if entry == example_entry():
                    self.assertContains(article, "Lemma 2")
                    self.assertContains(article, "Definition 2")
                    self.assertContains(article, "sumset-translation.svg")

    def test_named_cross_reference_and_return_link_target_specific_results(self):
        source = entries()["thm-triple-sumset-lower-bound"]
        source_url = reverse("catalog:entry", args=[source["id"]])
        parser = LinkParser()
        parser.feed(self.client.get(source_url).content.decode())
        citation = next(anchor for anchor in parser.anchors
                        if urlsplit(anchor["href"]).fragment == "sumset-lower-bound")
        self.assertEqual(citation["text"], "Sumset lower bound")
        self.assertNotIn("Lemma 2", citation["text"])
        local = next(anchor for anchor in parser.anchors if anchor.get("class") == "lemma-reference"
                     and anchor["href"] == "#nonempty-triple-sumset")
        self.assertEqual(local["text"], "Lemma 1")
        response = self.client.get(citation["href"])
        self.assertEqual(
            response.context["return_url"], source_url + "#triple-sumset-lower-bound")
        self.assertContains(response, "Back to Adding three sets", count=2)
        self.assertContains(response, 'class="reading-return"')
        self.assertContains(response, 'id="sumset-lower-bound"')

    def test_next_entry_navigation_reaches_the_next_note_and_stops_at_the_end(self):
        first = example_entry()
        second = entries()["thm-triple-sumset-lower-bound"]
        first_url = reverse("catalog:entry", args=[first["id"]])
        second_url = reverse("catalog:entry", args=[second["id"]])
        parser = LinkParser()
        parser.feed(self.client.get(first_url).content.decode())
        links = [anchor for anchor in parser.anchors if anchor.get(
            "rel") == "next"]
        self.assertEqual(len(links), 1)
        self.assertEqual(links[0]["href"], second_url)
        self.assertIn("Next entry", links[0]["text"])
        self.assertIn(second["title"], links[0]["text"])
        response = self.client.get(links[0]["href"])
        self.assertEqual(response.status_code, 200)
        self.assertNotContains(response, 'rel="next"')
        self.assertContains(response, "Back to Sumsets")

    def test_next_entry_follows_area_order_and_skips_unrelated_entries(self):
        first = example_entry()
        second = entries()["thm-triple-sumset-lower-bound"]
        unrelated = {**first, "id": "unrelated",
                     "primary_area": "group-theory"}
        catalog = {item["id"]: item for item in [first, unrelated, second]}
        with patch("catalog.content.entries", return_value=catalog):
            self.assertEqual(next_entry(first), second)
            self.assertIsNone(next_entry(second))
            self.assertIsNone(next_entry(unrelated))

    def test_questions_are_collapsed_and_returning_to_an_answer_reopens_it(self):
        for entry in entries().values():
            url = reverse("catalog:entry", args=[entry["id"]])
            parser = LinkParser()
            parser.feed(self.client.get(url).content.decode())
            questions = [item for item in parser.details if item.get(
                "class") == "question-answer"]
            self.assertTrue(questions)
            self.assertTrue(
                all("open" not in question for question in questions))
        citation = next(anchor for anchor in parser.anchors
                        if urlsplit(anchor["href"]).fragment == "zero-summand")
        response = self.client.get(citation["href"])
        return_url = response.context["return_url"]
        self.assertEqual(urlsplit(return_url).fragment,
                         "strict-growth-question")
        returned = self.client.get(return_url)
        parser = LinkParser()
        parser.feed(returned.content.decode())
        answers = [item for item in parser.details if item.get(
            "class") == "question-answer"]
        self.assertEqual(sum("open" in item for item in answers), 1)

    def test_recorded_references_resolve_to_blocks(self):
        for entry in entries().values():
            for block in entry["blocks"]:
                for reference in block.get("references", []):
                    target = entries()[reference["entry_id"]]
                    self.assertIn(reference["block_id"],
                                  target["blocks_by_id"])

    def test_invalid_return_anchor_falls_back_to_the_source_article(self):
        source = entries()["thm-triple-sumset-lower-bound"]
        target = example_entry()
        target_url = reverse("catalog:entry", args=[target["id"]])
        for anchor in ["missing", "https://example.com/", "<script>"]:
            with self.subTest(anchor=anchor):
                response = self.client.get(
                    target_url, {"from": source["id"], "at": anchor})
                self.assertEqual(response.context["return_url"],
                                 reverse("catalog:entry", args=[source["id"]]))

    def test_direct_entry_and_invalid_return_sources_fall_back_to_its_area(self):
        for entry in entries().values():
            url = reverse("catalog:entry", args=[entry["id"]])
            for source in [None, "missing", "https://example.com/", "//example.com/", entry["id"]]:
                with self.subTest(entry=entry["id"], source=source):
                    response = self.client.get(
                        url, {} if source is None else {"from": source})
                    self.assertContains(response, "Back to Sumsets", count=2)
                    self.assertEqual(response.context["return_url"], area_link(
                        areas()["sumsets"])["url"])

    def test_entry_counts_include_descendants_but_not_unrelated_areas(self):
        for area_id in ["combinatorics", "additive-combinatorics", "sumsets"]:
            with self.subTest(area=area_id):
                self.assertEqual(area_link(areas()[area_id])["entry_count"], 2)
        self.assertEqual(area_link(areas()["algebra"])["entry_count"], 0)

    def test_browsing_does_not_load_the_math_renderer(self):
        self.assertNotContains(self.client.get("/"), "katex.min.js")
        self.assertNotContains(self.client.get(
            area_link(areas()["combinatorics"])["url"]), "katex.min.js")

    def test_unpopulated_leaf_has_a_useful_empty_state(self):
        response = self.client.get(area_link(areas()["group-theory"])["url"])
        self.assertContains(response, "There are no entries here yet")
        self.assertContains(response, "Explore another area")

    def test_unknown_and_misplaced_routes_return_a_readable_404(self):
        for debug in (True, False):
            with self.subTest(debug=debug), override_settings(DEBUG=debug):
                for url in ["/missing-page/", "/areas/missing/", "/areas/algebra/sumsets/",
                            "/entries/missing/", "/entries/thm-sumset-lower-bound/extra/"]:
                    with self.subTest(url=url):
                        response = self.client.get(url)
                        self.assertContains(
                            response, "A missing connection.", status_code=404)
                        self.assertTemplateUsed(response, "404.html")
                        self.assertTemplateUsed(response, "base.html")
                        self.assertEqual(
                            response.headers["X-Frame-Options"], "DENY")

    def test_placeholders_do_not_expose_write_endpoints(self):
        home = self.client.get("/")
        self.assertContains(home, 'data-placeholder="login"')
        self.assertContains(home, 'data-placeholder="submit"')
        self.assertNotContains(home, 'type="password"')
        self.assertEqual(self.client.post("/").status_code, 405)
        self.assertEqual(self.client.post("/submit/").status_code, 404)

    def test_self_hosted_rendering_assets_exist(self):
        for asset in ["css/site.css", "js/site.js", "js/math.js",
                      "entries/thm-sumset-lower-bound/sumset-translation.svg",
                      "vendor/katex/katex.min.js", "vendor/katex/katex.min.css",
                      "vendor/katex/contrib/auto-render.min.js", "vendor/katex/fonts/KaTeX_Main-Regular.woff2"]:
            with self.subTest(asset=asset):
                self.assertIsNotNone(finders.find(asset))
