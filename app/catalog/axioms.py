"""Declared mathematical assumptions and their permitted Lean kernel axioms."""

AXIOM_LABELS = {"choice": "AC"}
BASELINE_LEAN_AXIOMS = {"propext", "Quot.sound"}
EXTRA_LEAN_AXIOMS = {"choice": {"Classical.choice"}}


def check_axioms(value):
    if not isinstance(value, list):
        raise ValueError("axioms must be a list")
    seen = set()
    for axiom in value:
        if not isinstance(axiom, str) or axiom not in AXIOM_LABELS:
            raise ValueError(f"Unknown axiom: {axiom!r}")
        if axiom in seen:
            raise ValueError(f"Duplicate axiom: {axiom}")
        seen.add(axiom)
    return seen


def check_axiom_dependencies(graph, requirements):
    """Reject missing references or extra dependency axioms, grouped by source node."""
    for node, dependencies in graph.items():
        extra = {}
        for dependency in dependencies:
            if dependency not in requirements:
                raise ValueError(f"{node}: missing dependency {dependency}")
            missing = requirements[dependency] - requirements[node]
            for axiom in missing:
                extra.setdefault(axiom, []).append(dependency)
        if extra:
            details = "; ".join(
                f"{axiom} ({', '.join(sorted(dependencies))})"
                for axiom, dependencies in sorted(extra.items()))
            raise ValueError(
                f"{node}: dependencies require undeclared axioms: {details}")


def permits_lean_axioms(declared, actual):
    allowed = BASELINE_LEAN_AXIOMS.copy()
    for axiom in check_axioms(declared):
        allowed.update(EXTRA_LEAN_AXIOMS[axiom])
    return set(actual) <= allowed
