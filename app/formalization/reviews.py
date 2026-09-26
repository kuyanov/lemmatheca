"""Stable review hashes, separate from proof verification fingerprints."""

from datetime import datetime
import hashlib
import json
import re

from catalog.sources import ContentError


SHA256 = re.compile(r'[0-9a-f]{64}\Z')


def digest(value):
    return hashlib.sha256(json.dumps(
        value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()


def validate_review(review):
    if review is None:
        return
    if (not isinstance(review, dict) or set(review) != {'sha256', 'recorded_at'}
            or not isinstance(review['sha256'], str) or not SHA256.fullmatch(review['sha256'])):
        raise ContentError(
            'Node review must be null or a sha256 and recorded_at record')
    try:
        date = datetime.fromisoformat(review['recorded_at'])
        if date.utcoffset() is None:
            raise ValueError('Timezone required')
    except (TypeError, ValueError) as error:
        raise ContentError(
            'Review recorded_at must be an ISO timestamp with a timezone') from error


def declaration_hashes(records, names):
    """Hash each target's semantic graph, including referenced definition bodies.

    Cycles from inductives and recursors are handled as a set of named records.
    The Lean exporter omits theorem proofs and source-position metadata.
    """
    hashes = {name: digest(record['payload'])
              for name, record in records.items()}
    result = {}
    for name in names:
        seen, pending = set(), [name]
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            if current not in records:
                raise ContentError(f'Missing review snapshot for {current}')
            seen.add(current)
            pending.extend(records[current]['references'])
        result[name] = digest({'version': 1, 'declaration': name,
                               'constants': {key: hashes[key] for key in sorted(seen)}})
    return result


def review_target_hash(node, declaration_sha256):
    """Bind the human description to the declaration, independently of the node ID."""
    reviewed = {key: node[key] for key in ('description', 'declaration')}
    return digest({'version': 3, 'node': reviewed,
                   'declaration': declaration_sha256})
