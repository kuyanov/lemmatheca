from django.urls import include, path

urlpatterns = [path("", include("catalog.urls"))]
