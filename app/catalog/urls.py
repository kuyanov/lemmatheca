from django.urls import path

from . import views

app_name = "catalog"
urlpatterns = [
    path("", views.home, name="home"),
    path("areas/<path:path>/", views.area, name="area"),
    path("entries/<str:entry_id>/", views.entry, name="entry"),
    path("lean/<path:source>/", views.lean_file, name="lean_file"),
]
