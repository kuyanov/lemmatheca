from django.conf import settings
from django.http import Http404
from django.views.defaults import page_not_found


class Development404Middleware:
    """Use the site's HTML 404 in development, just as Django does in production."""

    def __init__(self, get_response):
        self.get_response = get_response

    def __call__(self, request):
        response = self.get_response(request)
        if (
            settings.DEBUG
            and response.status_code == 404
            and response.get("Content-Type", "").startswith("text/html")
        ):
            # DEBUG normally bypasses 404.html for both unmatched URLs and Http404.
            return page_not_found(request, Http404())
        return response
