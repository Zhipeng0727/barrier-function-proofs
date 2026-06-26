"""Importing this package registers every backend with backend_base's registry."""
from verif_agent.backends import sampling      # noqa: F401
from verif_agent.backends import z3_backend    # noqa: F401
from verif_agent.backends import interval_backend  # noqa: F401
from verif_agent.backends import dreal_backend  # noqa: F401
from verif_agent.backends import lean_backend   # noqa: F401
from verif_agent.backends import nn_backends    # noqa: F401
