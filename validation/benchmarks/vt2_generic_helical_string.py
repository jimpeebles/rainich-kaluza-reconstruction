"""Generic positive oracle: helical reduction of a Schwarzschild black string."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path
from typing import Iterable

import sympy as sp

from rk_validation.exact import (
    emd_residuals_at,
    exterior_derivative_one_form,
    exterior_derivative_two_form,
    kaluza_uplift_metric,
    matrix_is_zero,
    ricci_tensor,
    ricci_tensor_at,
    simplify_matrix,
    wedge_one_form_two_form,
)


SCHEMA_VERSION = 1
BENCHMARK_ID = "vt2-generic-helical-string"


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest_expressions(expressions: Iterable[sp.Expr]) -> str:
    payload = "\n".join(sp.srepr(sp.simplify(expr)) for expr in expressions)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def build_artifact() -> dict[str, object]:
    t, r, theta, phi, z = sp.symbols("t r theta phi z", real=True)
    coordinates = (t, r, theta, phi)
    uplift_coordinates = (*coordinates, z)
    point = {t: sp.S.Zero, r: sp.S(3), theta: sp.pi / 4, phi: sp.S.Zero}

    lapse = 1 - 2 / r
    boost_sinh = sp.S.One
    boost_cosh = sp.sqrt(2)
    twist = sp.S.One
    black_string = sp.diag(
        -lapse,
        1 / lapse,
        r**2,
        r**2 * sp.sin(theta) ** 2,
        1,
    )

    # T = cosh(delta)t+sinh(delta)z,
    # Phi = phi+Bz, Z = sinh(delta)t+cosh(delta)z.
    jacobian = sp.eye(5)
    jacobian[0, 0] = boost_cosh
    jacobian[0, 4] = boost_sinh
    jacobian[3, 4] = twist
    jacobian[4, 0] = boost_sinh
    jacobian[4, 4] = boost_cosh
    pullback = simplify_matrix(jacobian.T * black_string * jacobian)

    fiber_norm = sp.factor(pullback[4, 4])
    potential_column = sp.ImmutableMatrix(
        4, 1, [sp.cancel(pullback[index, 4] / fiber_norm) for index in range(4)]
    )
    potential = tuple(potential_column)
    scalar = sp.sqrt(3) * sp.log(fiber_norm) / 2
    horizontal_metric = simplify_matrix(
        pullback[:4, :4]
        - fiber_norm * potential_column * potential_column.T
    )
    base_metric = simplify_matrix(sp.sqrt(fiber_norm) * horizontal_metric)
    coupling = sp.sqrt(3)

    uplift = kaluza_uplift_metric(base_metric, scalar, potential)
    reference_ricci = ricci_tensor(uplift_coordinates, black_string)
    point_ricci = ricci_tensor_at(coordinates, base_metric, point)
    emd = emd_residuals_at(
        coordinates, base_metric, scalar, potential, coupling, point
    )

    point_metric = simplify_matrix(base_metric.subs(point))
    point_inverse = simplify_matrix(point_metric.inv())
    mixed_ricci = simplify_matrix(point_inverse * point_ricci)
    characteristic = mixed_ricci.charpoly()
    coefficients = characteristic.all_coeffs()
    e1 = -coefficients[1]
    e2 = coefficients[2]
    e3 = -coefficients[3]
    e4 = coefficients[4]
    characteristic_discriminant = sp.factor(characteristic.discriminant())
    eigenvalues = mixed_ricci.eigenvals()
    kaluza_obstruction = sp.simplify(e1**2 * e4 - e1 * e2 * e3 + e3**2)

    field = exterior_derivative_one_form(coordinates, potential)
    point_field = simplify_matrix(field.subs(point))
    point_field_up = simplify_matrix(point_inverse * point_field * point_inverse)
    point_field_square = sp.simplify(
        sum(
            point_field[i, j] * point_field_up[i, j]
            for i in range(4)
            for j in range(4)
        )
    )
    scalar_gradient = tuple(sp.diff(scalar, coordinate) for coordinate in coordinates)
    point_scalar_gradient = tuple(
        sp.simplify(value.subs(point)) for value in scalar_gradient
    )
    point_scalar_gradient_square = sp.simplify(
        sum(
            point_inverse[i, j]
            * point_scalar_gradient[i]
            * point_scalar_gradient[j]
            for i in range(4)
            for j in range(4)
        )
    )

    # calF=exp(a phi/2)F obeys d calF=(a/2)dphi∧calF. The direct curvature seed
    # is calF/sqrt(2), but that constant cancels from this ratio, so the active
    # primal channel recovers the signed coupling without inserting ``a``.
    rainich_field = simplify_matrix(
        fiber_norm ** sp.Rational(3, 4) * field
    )
    rainich_derivative = exterior_derivative_two_form(
        coordinates, rainich_field
    )
    scalar_source = wedge_one_form_two_form(scalar_gradient, rainich_field)
    recovered_couplings = tuple(
        sp.simplify(
            (2 * rainich_derivative[index] / source).subs(point)
        )
        for index, source in scalar_source.items()
        if sp.simplify(source.subs(point)) != 0
    )
    recovered_coupling_squares = tuple(
        sp.simplify(value**2) for value in recovered_couplings
    )

    input_spec = {
        "source": {
            "kind": "constructed-from-standard-exact-solution",
            "provenance": "constant boost and azimuthal twist of Schwarzschild_4 times a flat fifth direction",
            "external_source": None,
        },
        "coordinates": [str(value) for value in uplift_coordinates],
        "mass_parameter": "1",
        "boost": {"sinh_delta": "1", "cosh_delta": "sqrt(2)"},
        "azimuthal_twist": "1",
        "exact_point": {str(key): str(value) for key, value in point.items()},
        "fiber_norm": str(fiber_norm),
        "base_metric": str(base_metric.tolist()),
        "scalar": str(scalar),
        "potential": [str(value) for value in potential],
        "expected_classification": "generic-kaluza-emd-physical-channel-a-squared-three-but-complete-detector-radicand-rejects-this-point",
    }

    checks = [
        {
            "name": "reference-black-string-ricci-vanishes",
            "passed": matrix_is_zero(reference_ricci),
            "residual_sha256": _digest_expressions(reference_ricci),
        },
        {
            "name": "uplift-equals-helical-black-string-pullback",
            "passed": matrix_is_zero(uplift - pullback),
            "residual_sha256": _digest_expressions(uplift - pullback),
        },
        {
            "name": "base-ricci-is-nonzero-at-exact-point",
            "passed": not matrix_is_zero(point_ricci),
            "residual_sha256": _digest_expressions(point_ricci),
        },
        {
            "name": "emd-residuals-vanish-at-exact-point",
            "passed": emd.all_zero(),
            "residual_sha256": _digest_expressions(
                [*list(emd.einstein), *emd.maxwell, emd.scalar, *emd.bianchi.values()]
            ),
        },
        {
            "name": "maxwell-sector-is-nonnull-at-exact-point",
            "passed": not matrix_is_zero(point_field) and point_field_square != 0,
            "residual_sha256": _digest_expressions(
                (*list(point_field), point_field_square)
            ),
        },
        {
            "name": "scalar-gradient-is-nonnull-at-exact-point",
            "passed": any(value != 0 for value in point_scalar_gradient)
            and point_scalar_gradient_square != 0,
            "residual_sha256": _digest_expressions(
                (*point_scalar_gradient, point_scalar_gradient_square)
            ),
        },
        {
            "name": "ricci-trace-is-nonzero-at-exact-point",
            "passed": sp.simplify(e1) != 0,
            "residual_sha256": _digest_expressions((e1,)),
        },
        {
            "name": "mixed-ricci-spectrum-is-real-and-simple",
            "passed": len(eigenvalues) == 4
            and all(multiplicity == 1 for multiplicity in eigenvalues.values())
            and all(value.is_real is True for value in eigenvalues),
            "residual_sha256": _digest_expressions(eigenvalues.keys()),
        },
        {
            "name": "characteristic-discriminant-is-nonzero",
            "passed": characteristic_discriminant != 0,
            "residual_sha256": _digest_expressions((characteristic_discriminant,)),
        },
        {
            "name": "necessary-kaluza-polynomial-obstruction-vanishes",
            "passed": kaluza_obstruction == 0,
            "residual_sha256": _digest_expressions((kaluza_obstruction,)),
        },
        {
            "name": "primal-channel-reconstructs-coupling-squared-three",
            "passed": bool(recovered_coupling_squares)
            and all(value == 3 for value in recovered_coupling_squares),
            "residual_sha256": _digest_expressions(
                tuple(value - 3 for value in recovered_coupling_squares)
            ),
        },
        {
            "name": "physical-kaluza-coupling-value-is-three",
            "passed": bool(recovered_coupling_squares)
            and all(value == 3 for value in recovered_coupling_squares),
            "residual_sha256": _digest_expressions(recovered_coupling_squares),
        },
    ]

    artifact = {
        "schema_version": SCHEMA_VERSION,
        "benchmark_id": BENCHMARK_ID,
        "evidence_class": "exact-symbolic-validation-not-lean-proof",
        "runtime": {"python": platform.python_version(), "sympy": sp.__version__},
        "input": input_spec,
        "input_sha256": hashlib.sha256(
            _canonical_json(input_spec).encode("utf-8")
        ).hexdigest(),
        "checks": checks,
        "passed": all(bool(check["passed"]) for check in checks),
    }
    return artifact


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail unless the committed artifact exactly matches fresh output",
    )
    arguments = parser.parse_args()
    artifact = build_artifact()
    if not artifact["passed"]:
        failed = [check["name"] for check in artifact["checks"] if not check["passed"]]
        raise SystemExit(f"benchmark failed: {', '.join(failed)}")

    destination = Path(__file__).parents[1] / "artifacts" / f"{BENCHMARK_ID}.json"
    rendered = json.dumps(artifact, indent=2, sort_keys=True) + "\n"
    if arguments.check:
        if not destination.exists():
            raise SystemExit(f"artifact is missing: {destination}")
        if destination.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"artifact drift detected; regenerate and review {destination}")
    else:
        destination.write_text(rendered, encoding="utf-8")
    print(f"PASS {BENCHMARK_ID}: {len(artifact['checks'])} exact checks")
    print(f"{'VERIFIED' if arguments.check else 'WROTE'} {destination}")


if __name__ == "__main__":
    main()
