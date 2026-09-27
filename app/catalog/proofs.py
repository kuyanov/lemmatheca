"""Build Lean and prepare proof results and entry summaries before saving them."""

import json
import re
import subprocess
from pathlib import Path
from tempfile import NamedTemporaryFile

from .entry_files import entry_ids, read_entry, save_entries
from .node_files import TOOLCHAIN_MODULES, prepare_results, read_nodes, save_results
from .progress import entry_progress
from .sources import parse_source

MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def build(corpus, formal):
    nodes = read_nodes(corpus)
    results = {}
    bound = [node for node in nodes.values() if node.get("declaration")]
    modules = {node.get("module") for node in bound}
    if any(not isinstance(module, str) or not MODULE.fullmatch(module) for module in modules):
        raise ValueError("Every declaration needs a valid Lean module.")
    # Core modules are already supplied by the toolchain, not Lake targets.
    build_modules = sorted(module for module in modules
                           if module.split(".")[0] not in TOOLCHAIN_MODULES)
    subprocess.run(["lake", "build", "Lemmatheca", *
                   build_modules], cwd=formal, check=True)
    declarations = {node["declaration"] for node in bound}
    source = "\n".join(f"import {module}" for module in sorted(
        modules | {"Lemmatheca.ProofStatus"}))
    source += "\n" + \
        "\n".join(f"#node_status {json.dumps(name, ensure_ascii=False)}" for name in sorted(
            declarations)) + "\n"
    with NamedTemporaryFile(mode="w", suffix=".lean", encoding="utf-8", dir=formal, delete=False) as file:
        path = Path(file.name)
        file.write(source)
    try:
        check = subprocess.run(["lake", "env", "lean", path.name], cwd=formal, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
    finally:
        path.unlink(missing_ok=True)
    for line in check.stdout.splitlines():
        if line.startswith("NODE_STATUS "):
            result = json.loads(line.removeprefix("NODE_STATUS "))
            name = result.pop("declaration")
            if name in results or type(result.get("verified")) is not bool:
                raise ValueError(f"Invalid Lean proof result: {name}")
            results[name] = result
    if results.keys() != declarations:
        raise ValueError(
            "Lean did not report every registered declaration.")
    updated = prepare_results(corpus, nodes, results)
    entries = {}
    for identifier in entry_ids(corpus):
        entry = read_entry(identifier, corpus)
        blocks, *_ = parse_source(entry.pop("source"))
        entry.pop("directory")
        entry["formalization"] = entry_progress(blocks, updated)
        entries[identifier] = entry
    # Validate every summary against the new proof results before writing either.
    verified = save_results(corpus, updated)
    save_entries(corpus, entries)
    return verified, len(nodes)
