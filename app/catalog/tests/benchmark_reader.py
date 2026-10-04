"""Run with: python app/manage.py shell -c 'from catalog.tests.benchmark_reader import benchmark; benchmark()'."""

from collections import Counter
import json
from math import ceil
from pathlib import Path
from statistics import median
from time import perf_counter
from unittest.mock import patch

from django.conf import settings
from django.test import Client, override_settings


PATHS = (
    "/",
    "/areas/logic-and-foundations/",
    "/areas/logic-and-foundations/set-theory/",
    "/entries/sets-and-maps/",
    "/entries/ordered-sets/",
    "/nodes/set-subset-transitive/",
    "/api/nodes/set-subset-transitive/",
)


def benchmark(samples=50, warmup=5):
    """Measure full Django responses, excluding HTTP transport and static assets."""
    client = Client()
    report = {"samples": samples, "warmup": warmup,
              "debug": False, "routes": {}}
    with override_settings(DEBUG=False, ALLOWED_HOSTS=["testserver"]):
        for url in PATHS:
            for _ in range(warmup):
                assert client.get(url).status_code == 200, url
            times = []
            for _ in range(samples):
                start = perf_counter()
                response = client.get(url)
                times.append((perf_counter() - start) * 1000)
                assert response.status_code == 200, url
            reads = Counter()
            original_open = Path.open

            def opened(path, *args, **kwargs):
                if path.is_relative_to(settings.CORPUS_DIR):
                    reads[str(path.relative_to(settings.CORPUS_DIR))] += 1
                return original_open(path, *args, **kwargs)

            # Instrument separately so file counting does not affect timings.
            with patch.object(Path, "open", opened):
                assert client.get(url).status_code == 200, url
            report["routes"][url] = {
                "median_ms": round(median(times), 3),
                "p95_ms": round(sorted(times)[ceil(samples * .95) - 1], 3),
                "corpus_reads": reads.total(),
                "unique_corpus_files": len(reads),
            }
    print(json.dumps(report, indent=2))
    return report
