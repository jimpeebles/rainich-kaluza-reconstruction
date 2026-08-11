"""Exact symbolic validation utilities for the Rainich--Kaluza program.

This package produces reproducible computational evidence.  It is deliberately
separate from the Lean sources, which remain the repository's proof layer.
"""

from .exact import (
    EMDResiduals,
    christoffel_symbols,
    emd_residuals,
    exterior_derivative_one_form,
    kaluza_uplift_metric,
    ricci_tensor,
    scalar_curvature,
)

__all__ = [
    "EMDResiduals",
    "christoffel_symbols",
    "emd_residuals",
    "exterior_derivative_one_form",
    "kaluza_uplift_metric",
    "ricci_tensor",
    "scalar_curvature",
]
