"""The deliberately small entry metadata contract."""

import re
from urllib.parse import urlsplit

from .sources import ContentError

ENTRY_FIELDS = {'id', 'title', 'based_on', 'primary_area', 'additional_areas',
                'status', 'reading_time', 'summary', 'abstract'}
CITATION_FIELDS = {'authors', 'title'}
CITATION_OPTIONAL_FIELDS = {'year', 'venue',
                            'volume', 'issue', 'pages', 'doi', 'url'}


def fields(value, required, optional=frozenset()):
    if not isinstance(value, dict) or not required <= value.keys() or value.keys() - required - optional:
        raise ContentError(f"Expected fields: {', '.join(sorted(required))}")


def validate_citation(citation):
    fields(citation, CITATION_FIELDS, CITATION_OPTIONAL_FIELDS)
    if not isinstance(citation['authors'], list) or not citation['authors'] or not all(
            isinstance(name, str) and name.strip() for name in citation['authors']):
        raise ContentError('Citation authors must be a nonempty list of names')
    for key in ('title', 'venue', 'volume', 'issue', 'pages', 'doi', 'url'):
        if key in citation and (not isinstance(citation[key], str) or not citation[key].strip()):
            raise ContentError(f'Citation {key} must be nonempty text')
    if 'year' in citation and (type(citation['year']) is not int or citation['year'] <= 0):
        raise ContentError('Citation year must be a positive integer')
    if 'doi' in citation and not re.fullmatch(r'10\.\d{4,9}/\S+', citation['doi']):
        raise ContentError(
            'Use a bare DOI, for example 10.1112/jlms/s1-34.3.352')
    if 'url' in citation:
        url = urlsplit(citation['url'])
        if url.scheme not in ('http', 'https') or not url.netloc:
            raise ContentError('A citation needs an HTTP(S) URL')


def validate_entry_metadata(entry):
    fields(entry, ENTRY_FIELDS)
    for key in ('id', 'title', 'primary_area', 'status', 'summary', 'abstract'):
        if not isinstance(entry[key], str) or not entry[key].strip():
            raise ContentError(f"{key} must be nonempty text")
    if not isinstance(entry['based_on'], list):
        raise ContentError('based_on must be a list of citations')
    for citation in entry['based_on']:
        validate_citation(citation)
    if not isinstance(entry['additional_areas'], list) or not all(
            isinstance(area, str) for area in entry['additional_areas']):
        raise ContentError('additional_areas must be a list of area IDs')
    if type(entry['reading_time']) is not int or entry['reading_time'] <= 0:
        raise ContentError('reading_time must be a positive number of minutes')
