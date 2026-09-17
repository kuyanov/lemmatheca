from django.urls import path

from . import views

app_name = "catalog"
urlpatterns = [
    path("", views.home, name="home"),
    path("areas/<path:path>/", views.area, name="area"),
    path("entries/<slug:entry_id>/<slug:slug>/", views.entry, name="entry"),
]
