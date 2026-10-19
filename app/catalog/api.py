"""Read-only authoring queries over the index and directly loaded corpus records."""

from functools import wraps

from django.conf import settings
from django.http import JsonResponse
from django.views.decorators.http import require_safe

from .index_reader import IndexUnavailable, get_index
from .queries import CorpusQuery, QueryError


def _error(code, message, status):
    return JsonResponse({"error": {"code": code, "message": message}}, status=status)


def _endpoint(*parameters, repeatable=()):
    allowed = set(parameters) | {"revision"}
    repeatable = set(repeatable)

    def decorate(view):
        @require_safe
        @wraps(view)
        def handle(request, *args, **kwargs):
            try:
                unknown = request.GET.keys() - allowed
                if unknown:
                    raise QueryError(f"Unknown query parameters: {', '.join(sorted(unknown))}")
                if any(key not in repeatable and len(request.GET.getlist(key)) != 1
                       for key in request.GET):
                    raise QueryError("Query parameters must not be repeated.")
                expected = request.GET.get("revision")
                if expected is not None and (not expected or len(expected) > 128):
                    raise QueryError("revision must be a nonempty index revision.")
                index = get_index()
                if expected is not None and expected != index["revision"]:
                    raise QueryError("The corpus index revision has changed.",
                                     status=409, code="revision_mismatch")
                result = view(request, CorpusQuery(index, settings.CORPUS_DIR), *args, **kwargs)
                response = JsonResponse({"index_revision": index["revision"],
                                         "metadata_source": "live_corpus", **result})
                response["Cache-Control"] = "no-store"
                return response
            except QueryError as error:
                return _error(error.code, str(error), error.status)
            except IndexUnavailable as error:
                return _error("index_unavailable", str(error), 503)
            except (KeyError, IndexError, TypeError, AttributeError):
                return _error("index_unavailable",
                              "Invalid corpus index. Run python app/manage.py validate_corpus --write-index.", 503)
            except (OSError, ValueError):
                return _error("index_outdated",
                              "Corpus records could not be read. Run python app/manage.py validate_corpus --write-index.", 409)
        return handle
    return decorate


def _integer(request, name, default, *, minimum=0, maximum=None):
    try:
        value = int(request.GET.get(name, default))
    except (ValueError, TypeError) as error:
        raise QueryError(f"{name} must be an integer.") from error
    if value < minimum or (maximum is not None and value > maximum):
        bound = f"{minimum} to {maximum}" if maximum is not None else f"at least {minimum}"
        raise QueryError(f"{name} must be {bound}.")
    return value


def _pagination(request):
    return {"limit": _integer(request, "limit", 20, minimum=1, maximum=100),
            "offset": _integer(request, "offset", 0)}


def _boolean(request, name, default=None):
    value = request.GET.get(name)
    if value is None:
        return default
    if value.casefold() in {"true", "1"}:
        return True
    if value.casefold() in {"false", "0"}:
        return False
    raise QueryError(f"{name} must be true or false.")


def _csv(value):
    return [item.strip() for item in value.split(",")] if value else []


@_endpoint("area", "include_descendants", "fields", "limit", "offset")
def entry_list(request, query):
    return query.list_entries(
        area=request.GET.get("area"),
        include_descendants=_boolean(request, "include_descendants", True),
        fields=_csv(request.GET["fields"]) if "fields" in request.GET else None,
        **_pagination(request))


@_endpoint("include", "include_answers", "block_ids", "limit", "offset")
def entry_context(request, query, entry_id):
    include = _csv(request.GET["include"]) if "include" in request.GET else None
    block_ids = _csv(request.GET["block_ids"]) if "block_ids" in request.GET else None
    return query.get_entry_context(entry_id, include=include,
                                   include_answers=_boolean(request, "include_answers", True),
                                   block_ids=block_ids,
                                   **_pagination(request))


@_endpoint("q", "area", "kind", "include_answers", "limit", "offset")
def block_search(request, query):
    return query.search_blocks(request.GET.get("q", ""), area=request.GET.get("area"),
                               kind=request.GET.get("kind"),
                               include_answers=_boolean(request, "include_answers", False),
                               **_pagination(request))


@_endpoint("q", "declaration", "module", "verified", "area", "include_descendants",
           "usage", "fields", "limit", "offset", repeatable=("q",))
def node_search(request, query):
    return query.find_nodes(
        queries=request.GET.getlist("q") or [""],
        declaration=request.GET.get("declaration"), module=request.GET.get("module"),
        verified=_boolean(request, "verified"), area=request.GET.get("area"),
        include_descendants=_boolean(request, "include_descendants", True),
        usage=request.GET.get("usage", "any"),
        fields=_csv(request.GET["fields"]) if "fields" in request.GET else None,
        **_pagination(request))


@_endpoint("target", "direction", "limit", "offset")
def references(request, query):
    if not request.GET.get("target"):
        raise QueryError("target is required.")
    return query.get_references(request.GET["target"], direction=request.GET.get("direction", "both"),
                                **_pagination(request))


@_endpoint("entry_ids")
def coverage(request, query):
    return query.get_coverage(_csv(request.GET.get("entry_ids", "")))


@_endpoint("limit", "offset")
def node_consumers(request, query, node_id):
    return query.get_node_consumers(node_id, **_pagination(request))
