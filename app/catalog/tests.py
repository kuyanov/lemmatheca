from html.parser import HTMLParser

from django.contrib.staticfiles import finders
from django.test import SimpleTestCase, override_settings
from django.urls import reverse

from .content import ancestors, area_link, areas, children, example_entry


class LinkParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []

    def handle_starttag(self, tag, attrs):
        if tag == "a":
            self.links.extend(value for name, value in attrs if name == "href")


class CatalogTests(SimpleTestCase):
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
        urls = [reverse("catalog:home"), *(area_link(area)["url"] for area in areas().values())]
        for url in urls:
            parser = LinkParser()
            parser.feed(self.client.get(url).content.decode())
            for link in parser.links:
                if link.startswith("/"):
                    with self.subTest(source=url, target=link):
                        self.assertEqual(self.client.get(link).status_code, 200)

    def test_example_appears_at_the_correct_leaf(self):
        entry = example_entry()
        url = reverse("catalog:entry", args=[entry["id"], entry["slug"]])
        response = self.client.get(area_link(areas()["sumsets"])["url"])
        self.assertContains(response, url)
        proof = self.client.get(url)
        self.assertContains(proof, 'id="proof"')
        self.assertContains(proof, "sumset-translation.svg")
        self.assertContains(proof, "Example · draft")
        self.assertContains(proof, "has not yet been checked in Lean")
        self.assertContains(proof, "katex.min.js")

    def test_browsing_does_not_load_the_math_renderer(self):
        self.assertNotContains(self.client.get("/"), "katex.min.js")
        self.assertNotContains(self.client.get(area_link(areas()["combinatorics"])["url"]), "katex.min.js")

    def test_unpopulated_leaf_has_a_useful_empty_state(self):
        response = self.client.get(area_link(areas()["group-theory"])["url"])
        self.assertContains(response, "There are no entries here yet")
        self.assertContains(response, "Explore another area")

    def test_unknown_and_misplaced_routes_return_a_readable_404(self):
        for debug in (True, False):
            with self.subTest(debug=debug), override_settings(DEBUG=debug):
                for url in ["/missing-page/", "/areas/missing/", "/areas/algebra/sumsets/",
                            "/entries/missing/missing/"]:
                    with self.subTest(url=url):
                        response = self.client.get(url)
                        self.assertContains(response, "A missing connection.", status_code=404)
                        self.assertTemplateUsed(response, "404.html")
                        self.assertTemplateUsed(response, "base.html")
                        self.assertEqual(response.headers["X-Frame-Options"], "DENY")

    def test_placeholders_do_not_expose_write_endpoints(self):
        home = self.client.get("/")
        self.assertContains(home, 'data-placeholder="login"')
        self.assertContains(home, 'data-placeholder="submit"')
        self.assertNotContains(home, 'type="password"')
        self.assertEqual(self.client.post("/").status_code, 405)
        self.assertEqual(self.client.post("/submit/").status_code, 404)

    def test_self_hosted_rendering_assets_exist(self):
        for asset in ["css/site.css", "js/site.js", "js/math.js", "images/sumset-translation.svg",
                      "vendor/katex/katex.min.js", "vendor/katex/katex.min.css",
                      "vendor/katex/contrib/auto-render.min.js", "vendor/katex/fonts/KaTeX_Main-Regular.woff2"]:
            with self.subTest(asset=asset):
                self.assertIsNotNone(finders.find(asset))
