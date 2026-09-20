"""Strict JSON loading shared by the human and formal catalogs."""

import json

from .sources import ContentError


def read_json(path):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ContentError(f"{path}: duplicate JSON key {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique_object)

