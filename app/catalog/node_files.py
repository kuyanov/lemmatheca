"""Read authored node JSON and installed Lean source files."""

import os
from pathlib import Path
import re

from django.conf import settings

from .files import read_json, read_record

LEAN_MODULE = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*\Z")
TOOLCHAIN_MODULES = {"Init", "Lean", "Std"}


def read_nodes(corpus):
    return {identifier: read_node(identifier, corpus) for identifier in node_ids(corpus)}


def node_ids(corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    return [path.stem for path in sorted((corpus / "nodes").glob("*.json"))]


def read_node(identifier, corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    return read_record(corpus / "nodes" / f"{identifier}.json", identifier)


def source_for_module(module):
    source = module.replace(".", "/") + ".lean"
    return "formal/" + source if module.split(".")[0] == "Lemmatheca" else source


def source_path(module, root):
    source = source_for_module(module)
    namespace = module.split(".")[0]
    if namespace == "Lemmatheca":
        directory, relative = root / "formal", source.removeprefix("formal/")
    elif namespace in TOOLCHAIN_MODULES:
        version = (
            root / "formal/lean-toolchain").read_text().strip().split(":")[-1]
        elan = Path(os.environ.get(
            "ELAN_HOME", Path.home() / ".elan")).expanduser()
        directory = elan / "toolchains" / \
            f"leanprover--lean4---{version}" / "src/lean"
        relative = source
    else:
        packages = read_json(root / "formal/lake-manifest.json")["packages"]
        package = next(
            (package for package in packages if package["name"].lower() == namespace.lower()), None)
        if package is None:
            raise FileNotFoundError(
                f"No installed package for Lean module: {module}")
        directory = root / "formal/.lake/packages" / package["name"]
        relative = source
    return directory / relative


def read_source(module, root):
    return source_path(module, root).read_text(encoding="utf-8").splitlines()
