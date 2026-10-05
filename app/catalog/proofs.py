"""Build Lean and prepare proof results and entry summaries before saving them."""

import json
import re
import subprocess
from pathlib import Path
from tempfile import NamedTemporaryFile

from .axioms import check_axiom_dependencies, check_axioms
from .entry_files import entry_ids, read_entry, save_entries
from .node_files import TOOLCHAIN_MODULES, prepare_results, read_nodes, save_results
from .progress import entry_progress
from .sources import parse_source

MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def build(corpus, formal):
    nodes = read_nodes(corpus)
    for node in nodes.values():
        check_axioms(node.get("axioms"))
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
            if not isinstance(result, dict) or not isinstance(result.get("declaration"), str):
                raise ValueError(
                    "Invalid Lean proof result: missing declaration name")
            name = result.pop("declaration")
            if name in results or type(result.get("verified")) is not bool:
                raise ValueError(f"Invalid Lean proof result: {name}")
            if result.keys() - {"verified", "lean_axioms", "signature", "module", "declaration_line"}:
                raise ValueError(
                    f"Unexpected Lean proof result fields: {name}")
            axioms = result.get("lean_axioms")
            if (not isinstance(axioms, list)
                    or any(not isinstance(axiom, str) or not axiom for axiom in axioms)
                    or len(set(axioms)) != len(axioms)):
                raise ValueError(f"Invalid Lean axiom result: {name}")
            results[name] = result
    if results.keys() != declarations:
        raise ValueError(
            "Lean did not report every registered declaration.")
    updated = prepare_results(corpus, nodes, results)
    # Invalid hints or allowance mismatches prevent all writes. Verification above
    # independently checks actual Lean axioms against each node's own allowance.
    check_axiom_dependencies(
        {identifier: node.get("dependencies", [])
         for identifier, node in updated.items()},
        {identifier: set(node["axioms"]) for identifier, node in updated.items()})
    entries = {}
    for identifier in entry_ids(corpus):
        entry = read_entry(identifier, corpus)
        blocks, *_ = parse_source(entry.pop("source"), validate=True)
        entry.pop("directory")
        for block in blocks:
            for node_id in block["formal_ids"] or []:
                if node_id not in updated:
                    raise ValueError(
                        f"{identifier}: unknown formal node: {node_id}")
        entry["formalization"] = entry_progress(blocks, updated)
        entries[identifier] = entry
    # Prepare every proof result and entry summary before writing.
    verified = save_results(corpus, updated)
    save_entries(corpus, entries)
    return verified, len(nodes)
