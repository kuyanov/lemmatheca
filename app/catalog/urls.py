from django.urls import path

from . import views

app_name = "catalog"
urlpatterns = [
    path("", views.home, name="home"),
    path("areas/<path:path>/", views.area, name="area"),
    path("entries/<str:entry_id>/", views.entry, name="entry"),
    path("formal/nodes/<str:node_id>/", views.node_page, name="node"),
    path("api/formal/nodes/", views.node_list, name="node_list"),
    path("api/formal/nodes/<str:node_id>/",
         views.node_detail, name="node_detail"),
]
