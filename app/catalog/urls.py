from django.urls import path

from . import api, views

app_name = "catalog"
urlpatterns = [
    path("", views.home, name="home"),
    path("areas/<path:path>/", views.area, name="area"),
    path("entries/<str:entry_id>/", views.entry, name="entry"),
    path("nodes/<str:node_id>/", views.node_page, name="node"),
    path("api/nodes/", views.node_list, name="node_list"),
    path("api/nodes/<str:node_id>/",
         views.node_detail, name="node_detail"),
    path("api/entries/", api.entry_list, name="entry_list"),
    path("api/entries/<str:entry_id>/context/", api.entry_context, name="entry_context"),
    path("api/search/blocks/", api.block_search, name="block_search"),
    path("api/search/nodes/", api.node_search, name="node_search"),
    path("api/references/", api.references, name="references"),
    path("api/coverage/", api.coverage, name="coverage"),
    path("api/nodes/<str:node_id>/consumers/", api.node_consumers, name="node_consumers"),
    path("api/source-errors/sources/", api.source_reviews, name="source_reviews"),
    path("api/source-errors/sources/<str:record_id>/", api.source_review_detail,
         name="source_review_detail"),
    path("api/source-errors/findings/", api.source_findings, name="source_findings"),
    path("api/source-errors/findings/<str:record_id>/", api.source_finding_detail,
         name="source_finding_detail"),
    path("api/reference-planning/", api.reference_plans, name="reference_plans"),
    path("api/reference-planning/<str:record_id>/", api.reference_plan_detail,
         name="reference_plan_detail"),
]
