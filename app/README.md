# Web app

A small, server-rendered Django site. It has 12 top-level areas, nested subareas,
breadcrumbs, and an HTML sumset proof with locally rendered equations and an SVG
illustration. There is no browser framework, bundler, CDN, or remote font service.
KaTeX loads only on the mathematical article page.

From the repository root, with Python 3.12–3.14 and uv installed:

```sh
uv sync --locked
uv run python app/manage.py runserver
```

Open <http://127.0.0.1:8000/>. No database setup or migrations are needed.
This is a local development server, not a production deployment configuration.

Missing HTML pages render `app/templates/404.html` with HTTP status 404 in both
development and production. `Development404Middleware` replaces Django's technical
404 when `DEBUG=True`, so you can preview the real error page locally. Debug
tracebacks for server errors remain available. Restart a server launched with
`--noreload` after changing Python code or settings.

The example is under **Combinatorics → Additive combinatorics → Sumsets**:

<http://127.0.0.1:8000/entries/thm-sumset-lower-bound/sumset-lower-bound/>

The login and submit buttons open placeholder dialogs. They do not authenticate,
collect data, or submit proofs. The article is clearly marked as a draft: its
general inequality has not yet been formalized or accepted by a maintainer.

## Editing

| File | Purpose |
| --- | --- |
| `examples/taxonomy.json` | Area titles, descriptions, and parent relationships |
| `app/catalog/content.py` | Seed content lookup and navigation |
| `app/catalog/views.py` | Home, area, and statement pages |
| `app/templates/catalog/proofs/sumset_lower_bound.html` | Human proof as HTML, with LaTeX delimiters |
| `app/static/images/sumset-translation.svg` | Explanatory figure |
| `app/static/css/site.css` | Shared responsive styles and print layout |
| `app/static/js/site.js` | Placeholder dialogs |
| `app/static/js/math.js` | Math rendering configuration |
| `app/static/vendor/katex/` | Pinned KaTeX 0.18.7 scripts, fonts, and license |

Templates are trusted repository content. There is no user HTML upload or render
endpoint. Inline math uses `\(...\)` and display math uses `\[...\]`. KaTeX
generates accessible MathML alongside its visual layout. All referenced fonts
are self-hosted. Restart the server after editing the cached JSON seed data.

The navigation uses the shared seed taxonomy; only the sumset leaf contains an
example entry. Other leaves have an explicit empty state. The HTML proof is an
initial presentation fixture; the future corpus renderer will replace this
handwritten template when the submission/content pipeline is implemented.

## Checks

```sh
uv run python app/manage.py check
uv run python app/manage.py test catalog
```

The tests check every category route and rendered navigation link, correct example
placement, missing pages, empty leaves, read-only placeholders, and local math
assets. The general Lean project is independent of this web app.
