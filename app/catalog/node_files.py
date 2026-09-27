"""Read node JSON and Lean source files, and persist build results."""

import os
from pathlib import Path
import re

from django.conf import settings

from .files import read_json, read_record, records, write_json

LEAN_MODULE = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*\Z")
TOOLCHAIN_MODULES = {"Init", "Lean", "Std"}


def read_nodes(corpus):
    return records(corpus, "node")


def node_ids(corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    return [path.stem for path in sorted((corpus / "nodes").glob("*.json"))]


def read_node(identifier, corpus=None):
    corpus = corpus or settings.CORPUS_DIR
    return read_record(corpus / "nodes" / f"{identifier}.json", identifier)


def source_for_module(module):
    if not isinstance(module, str) or not LEAN_MODULE.fullmatch(module):
        raise ValueError("Invalid Lean source module")
    source = module.replace(".", "/") + ".lean"
    return "formal/" + source if module.split(".")[0] == "Lemmatheca" else source


def read_source(module, root):
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
            package for package in packages if package["name"].lower() == namespace.lower())
        directory = root / "formal/.lake/packages" / package["name"]
        relative = source
    path = directory / relative
    if not path.resolve().is_relative_to(directory.resolve()):
        raise ValueError("Lean source is outside its source tree")
    return path.read_text(encoding="utf-8").splitlines()


def save_results(corpus, nodes, results):
    verified = 0
    for identifier, node in nodes.items():
        path = corpus / "nodes" / f"{identifier}.json"
        record = read_json(path)
        # Preserve metadata edited while Lean was running.
        if (record.get("module"), record.get("declaration")) != (node.get("module"), node.get("declaration")):
            result = {"verified": False}
        else:
            result = results.get(node.get("declaration"), {"verified": False})
        for field in ("signature", "declaration_line"):
            record.pop(field, None)
        record.update(result)
        write_json(path, record)
        verified += record["verified"]
    return verified
