"""Saved proof results belong to the exact authored binding that Lean checked."""

from .node_files import LEAN_MODULE


PROOF_FIELDS = ("verified", "signature", "declaration_line")


def validate_result(result):
    if (not isinstance(result, dict)
            or not {"binding", "verified"} <= result.keys()
            or result.keys() - {"binding", *PROOF_FIELDS, "defining_module"}
            or type(result["verified"]) is not bool):
        raise ValueError("Invalid indexed node result")
    binding = result["binding"]
    if not isinstance(binding, list) or len(binding) != 2:
        raise ValueError("Invalid indexed node binding")
    module, declaration = binding
    if module is None and declaration is None:
        if result != {"binding": [None, None], "verified": False}:
            raise ValueError("An unbound node cannot have proof results")
        return
    if (not isinstance(module, str) or not LEAN_MODULE.fullmatch(module)
            or not isinstance(declaration, str) or not declaration.strip()):
        raise ValueError("Invalid indexed node binding")
    # Escaped lone surrogates are valid JSON but cannot be rendered or rebuilt.
    declaration.encode("utf-8")
    if "signature" in result and (not isinstance(result["signature"], str)
                                   or not result["signature"].strip()):
        raise ValueError("Invalid indexed node signature")
    if "signature" in result:
        result["signature"].encode("utf-8")
    if "declaration_line" in result and (type(result["declaration_line"]) is not int
                                          or result["declaration_line"] < 1):
        raise ValueError("Invalid indexed node declaration line")
    if "defining_module" in result and (not isinstance(result["defining_module"], str)
                                         or not LEAN_MODULE.fullmatch(result["defining_module"])):
        raise ValueError("Invalid indexed node defining module")


def saved_result(node, index):
    binding = [node.get("module"), node.get("declaration")]
    result = index.get("nodes", {}).get(node["id"], {})
    if all(binding) and result.get("binding") == binding:
        return result
    return {"binding": binding, "verified": False}


def with_node_result(node, index):
    result = saved_result(node, index)
    record = {key: value for key, value in node.items() if key not in PROOF_FIELDS}
    record.update({field: result[field] for field in PROOF_FIELDS if field in result})
    if "defining_module" in result:
        record["module"] = result["defining_module"]
    return record
