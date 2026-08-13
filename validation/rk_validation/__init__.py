"""Exact symbolic validation utilities for the Rainich--Kaluza program.

This package produces reproducible computational evidence.  It is deliberately
separate from the Lean sources, which remain the repository's proof layer.
"""

from .exact import (
    EMDResiduals,
    christoffel_symbols,
    effective_complexion_one_form,
    emd_residuals,
    exterior_derivative_one_form,
    kaluza_uplift_metric,
    next_order_sine_coupling_candidate,
    next_order_sine_residual,
    principal_reflection_covector,
    ricci_tensor,
    scalar_curvature,
)

__all__ = [
    "EMDResiduals",
    "christoffel_symbols",
    "effective_complexion_one_form",
    "emd_residuals",
    "exterior_derivative_one_form",
    "kaluza_uplift_metric",
    "next_order_sine_coupling_candidate",
    "next_order_sine_residual",
    "principal_reflection_covector",
    "ricci_tensor",
    "scalar_curvature",
]
