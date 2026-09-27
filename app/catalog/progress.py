"""Summarize saved verification flags for blocks and entries."""


def progress(groups, nodes):
    """Combine node lists; None means unplanned, while [] means not applicable."""
    ids = {identifier for group in groups for identifier in group or []}
    unknown = ids - nodes.keys()
    if unknown:
        raise ValueError(f"Unknown formal node: {sorted(unknown)[0]}")
    unplanned = sum(group is None for group in groups)
    complete = sum(nodes[identifier].get("verified", False) for identifier in ids)
    total = len(ids)
    if total:
        status = "complete" if complete == total and not unplanned else "partial"
    elif not unplanned:
        status = "not_applicable"
    else:
        status = "not_started" if unplanned == len(groups) else "partial"

    result = {"status": status, "complete": complete, "total": total, "unplanned": unplanned}
    if total and not unplanned:
        result["percent"] = complete * 100 // total
        label = f'{result["percent"]}%'
    else:
        label = {"not_started": "Not started", "not_applicable": "N/A", "partial": "Partial"}[status]

    if status == "not_started":
        description = "Formalization not started"
    elif status == "not_applicable":
        description = "Nothing to formalize"
    else:
        description = f"{complete} of {total} nodes verified" if total else "Formalization partial"
        if unplanned:
            description += f"; {unplanned} block{'s' if unplanned != 1 else ''} awaiting planning"
    return {**result, "label": label, "description": description}


def block_progress(ids, nodes):
    return progress([ids], nodes)


def entry_progress(blocks, nodes):
    return progress([block["formal_ids"] for block in blocks], nodes)
