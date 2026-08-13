"""Exact routing audit for the finite detector on the helical benchmark.

This benchmark is deliberately stricter than ``vt2_generic_helical_string``.
It evaluates the literal spectral ordering and scalar entrance used by
``IsActualMetricUpstreamEntranceAt4``.  It also records, gate by gate, where
the exact computation stops.  A passed artifact is therefore not a claim
that the replacement point is an accepted Lean detector instance.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path

import sympy as sp

from rk_validation.exact import (
    exterior_derivative_one_form,
    exterior_derivative_two_form,
    matrix_is_zero,
    ricci_tensor_at,
    simplify_matrix,
    wedge_one_form_two_form,
)
from rk_validation.helical_detector import (
    replacement_physical_active_certificate,
    replacement_scalar_closure_certificate,
    replacement_upstream_point_certificate,
)
from rk_validation.helical_fourth_order import (
    replacement_fourth_order_tower_certificate,
)


SCHEMA_VERSION = 1
BENCHMARK_ID = "vt2-complete-detector-route"
RAW_CHOICE_COUNT = 4**9 * 6 * 2**2


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest(*expressions: sp.Expr) -> str:
    payload = "\n".join(sp.srepr(sp.simplify(value)) for value in expressions)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _positive(value: sp.Expr) -> bool:
    return sp.ask(sp.Q.positive(sp.simplify(value))) is True


def _negative(value: sp.Expr) -> bool:
    return sp.ask(sp.Q.negative(sp.simplify(value))) is True


def _metric_fields() -> tuple[tuple[sp.Symbol, ...], sp.ImmutableMatrix, sp.Expr, tuple[sp.Expr, ...]]:
    t, r, theta, phi = sp.symbols("t r theta phi", real=True)
    coordinates = (t, r, theta, phi)
    sine = sp.sin(theta)
    denominator = r**3 * sine**2 + r + 2
    fiber_norm = denominator / r
    root = sp.sqrt(fiber_norm)
    metric = sp.ImmutableMatrix(
        [
            [
                root * ((4 - r) * denominator - 8) / (r * denominator),
                0,
                0,
                -2 * sp.sqrt(2) * r**2 * root * sine**2 / denominator,
            ],
            [0, r * root / (r - 2), 0, 0],
            [0, 0, r**2 * root, 0],
            [
                -2 * sp.sqrt(2) * r**2 * root * sine**2 / denominator,
                0,
                0,
                r**2 * root * (r + 2) * sine**2 / denominator,
            ],
        ]
    )
    scalar = sp.sqrt(3) * sp.log(fiber_norm) / 2
    potential = (
        2 * sp.sqrt(2) / denominator,
        sp.S.Zero,
        sp.S.Zero,
        r**3 * sine**2 / denominator,
    )
    return coordinates, metric, scalar, potential


def _spectral_point(radius: sp.Rational | sp.Integer) -> dict[str, object]:
    coordinates, metric, scalar, _ = _metric_fields()
    t, r, theta, phi = coordinates
    point = {t: sp.S.Zero, r: radius, theta: sp.pi / 4, phi: sp.S.Zero}
    G = simplify_matrix(metric.subs(point))
    Rcov = ricci_tensor_at(coordinates, metric, point)
    R = simplify_matrix(G.inv() * Rcov)
    characteristic = R.charpoly()
    coefficients = characteristic.all_coeffs()
    e1, e2, e3, e4 = (
        -coefficients[1],
        coefficients[2],
        -coefficients[3],
        coefficients[4],
    )
    q_sq = sp.simplify(-e3 / e1)
    residual_constant = sp.simplify(-e2 - q_sq)
    discriminant = sp.simplify(e1**2 + 4 * residual_constant)
    q = sp.sqrt(q_sq)
    root_a = sp.simplify((e1 - sp.sqrt(discriminant)) / 2)
    root_b = sp.simplify((e1 + sp.sqrt(discriminant)) / 2)
    identity = sp.eye(4)

    def projector(root_value: sp.Expr, others: tuple[sp.Expr, ...]) -> sp.ImmutableMatrix:
        numerator = identity
        denominator = sp.S.One
        for other in others:
            numerator = numerator * (R - other * identity)
            denominator *= root_value - other
        return simplify_matrix(numerator / denominator)

    projector_a = projector(root_a, (-q, root_b, q))
    projector_b = projector(root_b, (root_a, -q, q))
    diagonal_a = sp.simplify((root_a**2 - q_sq) / (root_a - root_b))
    diagonal_b = sp.simplify((root_b**2 - q_sq) / (root_b - root_a))
    algebraic = (
        matrix_is_zero(G.T - G)
        and _negative(G.det())
        and matrix_is_zero(G * G.inv() - identity)
        and matrix_is_zero((G * R).T - G * R)
        and e1 != 0
        and sp.simplify(e1**2 * e4 - e1 * e2 * e3 + e3**2) == 0
        and _positive(q_sq)
        and _positive(discriminant)
        and all(
            sp.simplify(left - right) != 0
            for left, right in (
                (root_a, -q),
                (root_a, root_b),
                (root_a, q),
                (-q, root_b),
                (-q, q),
                (root_b, q),
            )
        )
        and matrix_is_zero(projector_a * projector_a - projector_a)
        and matrix_is_zero(projector_b * projector_b - projector_b)
        and matrix_is_zero(projector_a * projector_b)
        and sp.simplify(sp.trace(projector_a) - 1) == 0
        and sp.simplify(sp.trace(projector_b) - 1) == 0
        and matrix_is_zero(R * projector_a - root_a * projector_a)
        and matrix_is_zero(R * projector_b - root_b * projector_b)
    )
    scalar_gradient = sp.ImmutableMatrix(
        [sp.simplify(sp.diff(scalar, coordinate).subs(point)) for coordinate in coordinates]
    )
    return {
        "point": point,
        "G": G,
        "R": R,
        "q_sq": q_sq,
        "root_a": root_a,
        "root_b": root_b,
        "projector_a": projector_a,
        "projector_b": projector_b,
        "diagonal_a": diagonal_a,
        "diagonal_b": diagonal_b,
        "algebraic": algebraic,
        "scalar_gradient": scalar_gradient,
    }


def _probe_norm(data: dict[str, object], projector_name: str, probe: int) -> sp.Expr:
    G = data["G"]
    projector = data[projector_name]
    assert isinstance(G, sp.MatrixBase) and isinstance(projector, sp.MatrixBase)
    vector = projector[:, probe]
    return sp.simplify((vector.T * G * vector)[0])


def _selected_scalar_at_replacement(data: dict[str, object]) -> sp.ImmutableMatrix:
    G = data["G"]
    PA = data["projector_a"]
    PB = data["projector_b"]
    u = data["diagonal_a"]
    v = data["diagonal_b"]
    assert all(isinstance(value, sp.MatrixBase) for value in (G, PA, PB))
    x_a = PA[:, 1]
    x_b = PB[:, 2]
    norm_a = sp.simplify((x_a.T * G * x_a)[0])
    norm_b = sp.simplify((x_b.T * G * x_b)[0])
    theta_a = simplify_matrix(G * x_a / sp.sqrt(-norm_a))
    theta_b = simplify_matrix(G * x_b / sp.sqrt(norm_b))
    # relativeMinus=false is vPlus=alpha+beta.
    return simplify_matrix(sp.sqrt(-2 * u) * theta_a + sp.sqrt(2 * v) * theta_b)


def _physical_primal_coupling_squares(radius: sp.Rational | sp.Integer) -> tuple[sp.Expr, ...]:
    coordinates, _, scalar, potential = _metric_fields()
    t, r, theta, phi = coordinates
    point = {t: sp.S.Zero, r: radius, theta: sp.pi / 4, phi: sp.S.Zero}
    denominator = r**3 * sp.sin(theta) ** 2 + r + 2
    fiber_norm = denominator / r
    field = exterior_derivative_one_form(coordinates, potential)
    rainich_field = simplify_matrix(fiber_norm ** sp.Rational(3, 4) * field)
    derivative = exterior_derivative_two_form(coordinates, rainich_field)
    scalar_gradient = tuple(sp.diff(scalar, coordinate) for coordinate in coordinates)
    source = wedge_one_form_two_form(scalar_gradient, rainich_field)
    recovered = (
        sp.simplify((2 * derivative[index] / value).subs(point))
        for index, value in source.items()
        if sp.simplify(value.subs(point)) != 0
    )
    return tuple(sp.simplify(value**2) for value in recovered)


def build_artifact() -> dict[str, object]:
    coordinates, metric, scalar, potential = _metric_fields()
    _, r, theta, _ = coordinates
    fiber_norm = (r**3 * sp.sin(theta) ** 2 + r + 2) / r
    committed = _spectral_point(sp.Integer(3))
    replacement = _spectral_point(sp.Rational(3, 2))
    committed_gate = sp.simplify(-2 * committed["diagonal_a"])
    replacement_gate_a = sp.simplify(-2 * replacement["diagonal_a"])
    replacement_gate_b = sp.simplify(2 * replacement["diagonal_b"])
    selected_scalar = _selected_scalar_at_replacement(replacement)
    scalar_gradient = replacement["scalar_gradient"]
    assert isinstance(scalar_gradient, sp.MatrixBase)
    physical_squares_3 = _physical_primal_coupling_squares(sp.Integer(3))
    physical_squares_replacement = _physical_primal_coupling_squares(sp.Rational(3, 2))
    closure = replacement_scalar_closure_certificate(coordinates, metric, scalar)
    upstream = replacement_upstream_point_certificate(
        replacement["G"],
        replacement["R"],
        replacement["q_sq"],
        scalar_gradient,
    )
    physical_active = replacement_physical_active_certificate(
        coordinates,
        metric,
        scalar,
        potential,
        fiber_norm,
        replacement["R"],
        replacement["q_sq"],
    )
    fourth_order = replacement_fourth_order_tower_certificate(
        coordinates,
        metric,
        scalar,
        potential,
        closure,
        physical_active,
    )

    checks = [
        {
            "name": "committed-point-algebraic-entrance-point-gates-pass",
            "passed": bool(committed["algebraic"]),
            "residual_sha256": _digest(committed["q_sq"], committed["root_a"], committed["root_b"]),
        },
        {
            "name": "committed-point-timelike-scalar-radicand-gate-fails",
            "passed": _negative(committed_gate),
            "residual_sha256": _digest(committed_gate),
        },
        {
            "name": "committed-point-complete-accepted-set-is-empty",
            "passed": _negative(committed_gate) and RAW_CHOICE_COUNT == 6_291_456,
            "reason": "the failed radicand gate is choice-independent and is a conjunct of every upstream entrance",
            "residual_sha256": _digest(committed_gate),
        },
        {
            "name": "committed-point-independent-physical-primal-channel-returns-three",
            "passed": bool(physical_squares_3) and all(value == 3 for value in physical_squares_3),
            "residual_sha256": _digest(*(value - 3 for value in physical_squares_3)),
        },
        {
            "name": "replacement-point-algebraic-entrance-point-gates-pass",
            "passed": bool(replacement["algebraic"]),
            "residual_sha256": _digest(replacement["q_sq"], replacement["root_a"], replacement["root_b"]),
        },
        {
            "name": "replacement-point-both-scalar-radicand-gates-pass",
            "passed": _positive(replacement_gate_a) and _positive(replacement_gate_b),
            "residual_sha256": _digest(replacement_gate_a, replacement_gate_b),
        },
        {
            "name": "replacement-point-selected-scalar-probe-signs-pass",
            "passed": _negative(_probe_norm(replacement, "projector_a", 1))
            and _positive(_probe_norm(replacement, "projector_b", 2)),
            "residual_sha256": _digest(
                _probe_norm(replacement, "projector_a", 1),
                _probe_norm(replacement, "projector_b", 2),
            ),
        },
        {
            "name": "replacement-point-literal-plus-scalar-candidate-equals-physical-gradient",
            "passed": matrix_is_zero(selected_scalar - scalar_gradient),
            "residual_sha256": _digest(*list(selected_scalar - scalar_gradient)),
        },
        {
            "name": "replacement-point-literal-plus-scalar-closure-obstruction-vanishes",
            "passed": bool(closure["full_closure_from_block_support"]),
            "reduction": closure["reduced_expression"],
            "raw_numerator_operations": closure["raw_numerator_operations"],
            "raw_expression_sha256": hashlib.sha256(
                str(closure["raw_expression"]).encode("utf-8")
            ).hexdigest(),
            "residual_sha256": _digest(sp.sympify(closure["reduced_expression"])),
        },
        {
            "name": "replacement-point-independent-physical-primal-channel-returns-three",
            "passed": bool(physical_squares_replacement)
            and all(value == 3 for value in physical_squares_replacement),
            "residual_sha256": _digest(*(value - 3 for value in physical_squares_replacement)),
        },
        {
            "name": "replacement-point-reconstruction-obstruction-vanishes",
            "passed": bool(upstream["reconstruction_zero"]),
            "residual_sha256": _digest(*list(upstream["reconstruction_obstruction"])),
        },
        {
            "name": "replacement-point-maxwell-residual-and-projector-entrance-passes",
            "passed": bool(upstream["maxwell_entrance"]),
            "identities": upstream["maxwell_checks"],
            "residual_sha256": _digest(
                *list(upstream["residual"] * upstream["residual"]
                    - replacement["q_sq"] * sp.eye(4)),
                *list((replacement["G"] * upstream["residual"]).T
                    - replacement["G"] * upstream["residual"]),
            ),
        },
        {
            "name": "replacement-point-selected-maxwell-frame-gates-pass",
            "passed": bool(upstream["frame_found"])
            and bool(upstream["pseudo_orthonormal"])
            and sp.simplify(upstream["frame_det"] + 16 * sp.sqrt(249) / 747) == 0
            and all(
                _negative(value) if index == 0 else _positive(value)
                for index, value in enumerate(upstream["frame_signs"])
            ),
            "choice": upstream["frame_choice"],
            "minus_candidate_count": upstream["minus_candidate_count"],
            "plus_candidate_count": upstream["plus_candidate_count"],
            "frame_signs": [str(value) for value in upstream["frame_signs"]],
            "frame_determinant": str(upstream["frame_det"]),
            "residual_sha256": _digest(
                *upstream["frame_signs"],
                upstream["frame_det"] + 16 * sp.sqrt(249) / 747,
            ),
        },
        {
            "name": "replacement-point-selected-oriented-coframe-and-hodge-gates-pass",
            "passed": bool(upstream["coframe_metric"])
            and bool(upstream["coframe_det_positive"])
            and sp.simplify(upstream["coframe_det"] - 3 * sp.sqrt(249) / 16) == 0
            and bool(upstream["hodge_compatible"]),
            "coframe_determinant": str(upstream["coframe_det"]),
            "residual_sha256": _digest(
                *list(upstream["hodge_obstruction"]),
                upstream["coframe_det"],
            ),
        },
        {
            "name": "replacement-point-physical-hodge-and-stress-align-with-detector",
            "passed": physical_active["local_density_squared"] == 0
            and bool(physical_active["local_density_positive"])
            and bool(physical_active["hodge_matches_literal_at_point"])
            and bool(physical_active["hodge_squares_to_minus_at_point"])
            and physical_active["double_angle_unit_circle"] == 0
            and bool(physical_active["physical_q_matches_detector"])
            and bool(physical_active["stress_matches_detector_residual"])
            and bool(physical_active["stress_square_matches_detector_q_sq"]),
            "local_density_at_point": str(physical_active["local_density_at_point"]),
            "physical_q_at_point": str(physical_active["physical_q_at_point"]),
            "residual_sha256": _digest(
                physical_active["local_density_squared"],
                physical_active["double_angle_unit_circle"],
                physical_active["physical_q_at_point"]
                    - physical_active["detector_q_at_point"],
            ),
        },
        {
            "name": "replacement-point-choice-free-physical-active-wedge-passes",
            "passed": bool(physical_active["active"]),
            "component": list(physical_active["active_component"]),
            "value": str(physical_active["active_value"]),
            "omega": [str(value) for value in physical_active["omega_at_point"]],
            "stress_scalar_action": [
                str(value) for value in physical_active["stress_scalar_action_at_point"]
            ],
            "residual_sha256": _digest(physical_active["active_value"]),
        },
        {
            "name": "replacement-point-literal-selected-scalar-and-residual-one-jets-match-physical",
            "passed": bool(
                fourth_order["literal_selected_scalar_one_jet_matches_physical"]
            )
            and bool(
                fourth_order["literal_residual_one_jet_matches_physical"]
            ),
            "tower_dimension": fourth_order["tower_dimension"],
            "residual_sha256": _digest(sp.S.Zero),
        },
        {
            "name": "replacement-point-selected-frame-one-jet-and-complete-channel-normal-form-pass",
            "passed": bool(fourth_order["selected_frame_orthonormal"])
            and bool(fourth_order["selected_coframe_inverse"])
            and fourth_order["complete_channel_residual_count"] == 0,
            "complete_channel_residual_count": fourth_order[
                "complete_channel_residual_count"
            ],
            "residual_sha256": _digest(
                sp.Integer(fourth_order["complete_channel_residual_count"])
            ),
        },
        {
            "name": "replacement-point-selected-literal-cosine-quotient-and-generic-component-pass",
            "passed": bool(fourth_order["source_nonzero"])
            and bool(fourth_order["active_wedge_nonzero"])
            and bool(fourth_order["literal_cosine_quotient_exact"]),
            "source_component": fourth_order["source_component"],
            "wedge_component": list(fourth_order["wedge_component"]),
            "cosine_value": fourth_order["cosine_value"],
            "residual_sha256": _digest(sp.S.Zero),
        },
        {
            "name": "replacement-point-physical-dA-is-exact-derivative-of-sqrt-three-cosine",
            "passed": bool(
                fourth_order[
                    "physical_dA_is_exact_derivative_of_sqrt_three_cosine"
                ]
            ),
            "physical_dA": fourth_order["physical_dA_value"],
            "residual_sha256": _digest(
                *physical_active[
                    "physical_cosine_coupling_derivative_at_point"
                ]
            ),
        },
        {
            "name": "replacement-point-physical-dA-fourth-order-residuals-and-output-three-pass",
            "passed": bool(fourth_order["physical_dA_sine_quotient_exact"])
            and bool(fourth_order["physical_dA_next_order_residuals_exact"])
            and bool(fourth_order["physical_dA_output_three_exact"]),
            "sine_value": fourth_order["sine_value"],
            "literal_quotient_derivative_bridge": fourth_order[
                "literal_quotient_derivative_equals_physical_dA"
            ],
            "residual_sha256": _digest(sp.S.Zero),
        },
    ]
    input_spec = {
        "source_benchmark": "vt2-generic-helical-string",
        "committed_point": {"r": "3", "theta": "pi/4"},
        "replacement_point": {"r": "3/2", "theta": "pi/4"},
        "raw_choice_count": RAW_CHOICE_COUNT,
        "replacement_scalar_choice_prefix": {
            "scalarTimelikeProbe": 1,
            "scalarSpacelikeProbe": 2,
            "relativeMinus": False,
        },
        "replacement_maxwell_choice_prefix": upstream["frame_choice"],
    }
    route_manifest = {
        "committed_point": [
            {"gate": "IsActualMetricAlgebraicEntranceAt4", "status": "passed-exact-pointwise"},
            {"gate": "timelike scalar amplitude 0 < -2*uA", "status": "failed-exact"},
            {"gate": "acceptedActualMetricFourthOrderDetectorChoicesAt", "status": "empty-by-shared-failed-conjunct"},
        ],
        "replacement_point": [
            {"gate": "IsActualMetricAlgebraicEntranceAt4", "status": "passed-exact-pointwise"},
            {"gate": "both scalar amplitude radicands", "status": "passed-exact"},
            {"gate": "selected scalar fixed-probe signs", "status": "passed-exact"},
            {"gate": "selected literal scalar candidate value", "status": "passed-exact-equals-dphi"},
            {"gate": "selected literal scalar closure first jet", "status": "passed-exact"},
            {"gate": "selected scalar reconstruction obstruction", "status": "passed-exact"},
            {"gate": "Maxwell residual/projector entrance", "status": "passed-exact"},
            {"gate": "selected finite Maxwell frame and four strict signs", "status": "passed-exact"},
            {"gate": "selected oriented coframe and literal metric-Hodge equality", "status": "passed-exact"},
            {"gate": "choice-free physical active wedge", "status": "passed-exact-component-1-2"},
            {
                "gate": "selected literal frame one-jet and complete first-order channels",
                "status": "passed-exact-128-dimensional-quadratic-tower",
            },
            {
                "gate": "literal quotient derivative equals physical dA",
                "status": "theorem-mediated-by-physical-germ-bridge-not-independently-expanded-as-a-second-jet",
            },
            {
                "gate": "complete fourth-order residuals and output",
                "status": "passed-exact-with-physical-dA-output-three",
            },
        ],
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "benchmark_id": BENCHMARK_ID,
        "evidence_class": "exact-symbolic-routing-certificate-not-lean-proof",
        "runtime": {"python": platform.python_version(), "sympy": sp.__version__},
        "input": input_spec,
        "input_sha256": hashlib.sha256(_canonical_json(input_spec).encode("utf-8")).hexdigest(),
        "checks": checks,
        "route_manifest": route_manifest,
        "passed": all(bool(check["passed"]) for check in checks),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    artifact = build_artifact()
    if not artifact["passed"]:
        failed = [check["name"] for check in artifact["checks"] if not check["passed"]]
        raise SystemExit(f"benchmark failed: {', '.join(failed)}")
    destination = Path(__file__).parents[1] / "artifacts" / f"{BENCHMARK_ID}.json"
    rendered = json.dumps(artifact, indent=2, sort_keys=True) + "\n"
    if arguments.check:
        if not destination.exists() or destination.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"artifact drift detected; regenerate and review {destination}")
    else:
        destination.write_text(rendered, encoding="utf-8")
    print(f"PASS {BENCHMARK_ID}: {len(artifact['checks'])} exact checks")
    print(f"{'VERIFIED' if arguments.check else 'WROTE'} {destination}")


if __name__ == "__main__":
    main()
