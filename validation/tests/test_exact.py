"""Regression tests for the transparent exact tensor formulas."""

from __future__ import annotations

import unittest

import sympy as sp

from benchmarks.vt1_flat_pure_gauge import build_artifact
from rk_validation.exact import (
    emd_residuals,
    kaluza_uplift_metric,
    matrix_is_zero,
    ricci_tensor,
    scalar_curvature,
)


class ExactTensorTests(unittest.TestCase):
    def test_minkowski_ricci_is_zero(self) -> None:
        coordinates = sp.symbols("t x y z", real=True)
        metric = sp.diag(-1, 1, 1, 1)
        self.assertTrue(matrix_is_zero(ricci_tensor(coordinates, metric)))

    def test_unit_sphere_ricci_and_scalar_sign(self) -> None:
        theta, phi = sp.symbols("theta phi", real=True)
        metric = sp.diag(1, sp.sin(theta) ** 2)
        ricci = ricci_tensor((theta, phi), metric)
        self.assertTrue(matrix_is_zero(ricci - metric))
        self.assertEqual(sp.simplify(scalar_curvature((theta, phi), metric)), 2)

    def test_zero_field_emd_residuals_are_zero(self) -> None:
        coordinates = sp.symbols("t x y z", real=True)
        metric = sp.diag(-1, 1, 1, 1)
        residuals = emd_residuals(
            coordinates,
            metric,
            sp.S.Zero,
            (sp.S.Zero,) * 4,
            sp.sqrt(3),
        )
        self.assertTrue(residuals.all_zero())

    def test_uplift_block_at_zero_fields(self) -> None:
        metric = sp.diag(-1, 1, 1, 1)
        uplift = kaluza_uplift_metric(metric, sp.S.Zero, (sp.S.Zero,) * 4)
        self.assertEqual(uplift, sp.diag(-1, 1, 1, 1, 1))

    def test_vt1_benchmark_passes(self) -> None:
        artifact = build_artifact()
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 8)


if __name__ == "__main__":
    unittest.main()
