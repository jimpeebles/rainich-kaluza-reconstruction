"""Regression tests for the transparent exact tensor formulas."""

from __future__ import annotations

import unittest

import sympy as sp

from benchmarks.vt1_flat_pure_gauge import build_artifact
from benchmarks.vt1b_boosted_black_string import build_artifact as build_vt1b_artifact
from benchmarks.vt1c_non_kaluza_dilaton import build_artifact as build_vt1c_artifact
from benchmarks.vt2_generic_helical_string import build_artifact as build_vt2_artifact
from benchmarks.vt2_complete_detector_route import (
    build_artifact as build_vt2_route_artifact,
)
from benchmarks.vt2b_generic_near_miss import build_artifact as build_vt2b_artifact
from rk_validation.exact import (
    effective_complexion_one_form,
    emd_residuals,
    emd_residuals_at,
    hodge_star_two_form,
    kaluza_uplift_metric,
    matrix_is_zero,
    next_order_sine_coupling_candidate,
    next_order_sine_residual,
    principal_reflection_covector,
    ricci_tensor,
    ricci_tensor_at,
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
        point_ricci = ricci_tensor_at(
            (theta, phi), metric, {theta: sp.pi / 4, phi: sp.S.Zero}
        )
        self.assertEqual(point_ricci, metric.subs(theta, sp.pi / 4))

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
        point_residuals = emd_residuals_at(
            coordinates,
            metric,
            sp.S.Zero,
            (sp.S.Zero,) * 4,
            sp.sqrt(3),
            dict.fromkeys(coordinates, sp.S.Zero),
        )
        self.assertTrue(point_residuals.all_zero())

    def test_uplift_block_at_zero_fields(self) -> None:
        metric = sp.diag(-1, 1, 1, 1)
        uplift = kaluza_uplift_metric(metric, sp.S.Zero, (sp.S.Zero,) * 4)
        self.assertEqual(uplift, sp.diag(-1, 1, 1, 1, 1))

    def test_lorentzian_hodge_star_squares_to_minus_one(self) -> None:
        metric = sp.diag(-1, 1, 1, 1)
        field = sp.zeros(4, 4)
        field[0, 1] = 1
        field[1, 0] = -1
        dual = hodge_star_two_form(metric, field)
        self.assertTrue(
            matrix_is_zero(hodge_star_two_form(metric, dual) + field)
        )

    def test_first_order_shear_and_fourth_order_coupling_recovery(self) -> None:
        scalar_covector = tuple(map(sp.Integer, (1, 2, 3, 5)))
        omega = tuple(map(sp.Integer, (2, -1, 4, 3)))
        sine_coupling = sp.Integer(4)
        cosine_coupling = sp.Integer(3)
        reflected = principal_reflection_covector(scalar_covector)
        eta = effective_complexion_one_form(
            omega, scalar_covector, sine_coupling
        )

        # The exact first-order shear leaves eta invariant while changing B.
        shear = sp.Rational(11, 7)
        shifted_omega = tuple(
            sp.simplify(component - shear * image / 2)
            for component, image in zip(omega, reflected, strict=True)
        )
        shifted_eta = effective_complexion_one_form(
            shifted_omega, scalar_covector, sine_coupling + shear
        )
        self.assertEqual(shifted_eta, eta)

        # Constancy of a gives dA=-2B omega and removes the shear ambiguity.
        cosine_derivative = tuple(
            sp.simplify(-2 * sine_coupling * component) for component in omega
        )
        recovered = next_order_sine_coupling_candidate(
            cosine_derivative, eta, scalar_covector, 0, 1
        )
        self.assertEqual(recovered, sine_coupling)
        self.assertEqual(
            next_order_sine_residual(
                cosine_derivative, eta, scalar_covector, recovered
            ),
            (sp.S.Zero,) * 4,
        )
        self.assertEqual(
            sp.simplify(cosine_coupling**2 + recovered**2),
            25,
        )

    def test_vt1_benchmark_passes(self) -> None:
        artifact = build_artifact()
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 8)

    def test_vt1b_benchmark_passes(self) -> None:
        artifact = build_vt1b_artifact()
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 9)

    def test_vt1c_benchmark_passes(self) -> None:
        artifact = build_vt1c_artifact()
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 9)

    def test_vt2_benchmark_passes(self) -> None:
        artifact = build_vt2_artifact()
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 12)

    def test_vt2_complete_detector_route_passes(self) -> None:
        artifact = build_vt2_route_artifact()
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 10)

    def test_vt2b_benchmark_passes(self) -> None:
        artifact = build_vt2b_artifact()
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 7)


if __name__ == "__main__":
    unittest.main()
