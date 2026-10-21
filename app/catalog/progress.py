"""Summarize saved verification flags for blocks and entries."""


def progress_counts(groups, nodes):
    """Count distinct nodes and blocks whose formal mapping is unspecified."""
    ids = {identifier for group in groups for identifier in group or []}
    return {"complete": sum(nodes.get(identifier, {}).get("verified", False) for identifier in ids),
            "total": len(ids), "unmapped_blocks": sum(group is None for group in groups)}


def format_progress(counts, block_count):
    """Derive presentation from compact counts and the known number of blocks."""
    complete, total, unmapped = (counts[key] for key in ("complete", "total", "unmapped_blocks"))
    if total:
        status = "complete" if complete == total and not unmapped else "partial"
    elif not unmapped:
        status = "not_applicable"
    else:
        status = "not_started" if unmapped == block_count else "partial"

    result = {**counts, "status": status}
    if total and not unmapped:
        result["percent"] = complete * 100 // total
        label = f'{result["percent"]}%'
    else:
        label = {"not_started": "Not started",
                 "not_applicable": "N/A", "partial": "Partial"}[status]

    if status == "not_started":
        description = "Formalization not started"
    elif status == "not_applicable":
        description = "Nothing to formalize"
    else:
        description = f"{complete} of {total} nodes verified" if total else "Formalization partial"
        if unmapped:
            description += f"; {unmapped} block{'s' if unmapped != 1 else ''} without formal-node mappings"
    return {**result, "label": label, "description": description}


def progress(groups, nodes):
    return format_progress(progress_counts(groups, nodes), len(groups))


def block_progress(ids, nodes):
    return progress([ids], nodes)


def entry_progress(blocks, nodes):
    return progress([block["formal_ids"] for block in blocks], nodes)
