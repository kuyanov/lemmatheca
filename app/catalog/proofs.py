"""Build one Lean project, then persist declaration-level proof results."""

import json
import re
import subprocess
from pathlib import Path
from tempfile import NamedTemporaryFile

from .node_files import TOOLCHAIN_MODULES, read_nodes, save_results

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
    return save_results(corpus, nodes, results), len(nodes)
