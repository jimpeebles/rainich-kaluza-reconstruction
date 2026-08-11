"""V-T1 exact benchmark: flat geometry in nonlinear and pure-gauge coordinates."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path
from typing import Iterable

import sympy as sp

from rk_validation.exact import (
    christoffel_symbols,
    emd_residuals,
    exterior_derivative_one_form,
    kaluza_uplift_metric,
    matrix_is_zero,
    ricci_tensor,
    simplify_matrix,
)


SCHEMA_VERSION = 1
BENCHMARK_ID = "vt1-flat-cylindrical-pure-gauge"


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest_expressions(expressions: Iterable[sp.Expr]) -> str:
    payload = "\n".join(sp.srepr(sp.simplify(expr)) for expr in expressions)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def build_artifact() -> dict[str, object]:
    t, r, theta, y, z = sp.symbols("t r theta y z", real=True)
    coordinates = (t, r, theta, y)
    uplift_coordinates = (*coordinates, z)
    base_metric = sp.diag(-1, 1, r**2, 1)
    scalar = sp.S.Zero
    coupling = sp.sqrt(3)

    gauge_function = r * y
    potential = tuple(sp.diff(gauge_function, coordinate) for coordinate in coordinates)
    field = exterior_derivative_one_form(coordinates, potential)
    uplift = kaluza_uplift_metric(base_metric, scalar, potential)

    # Pull back diag(-1, 1, r^2, 1, 1) under z' = z + r y.
    reference_metric = sp.diag(-1, 1, r**2, 1, 1)
    jacobian = sp.eye(5)
    for index, coordinate in enumerate(coordinates):
        jacobian[4, index] = sp.diff(gauge_function, coordinate)
    pullback = simplify_matrix(jacobian.T * reference_metric * jacobian)

    base_gamma = christoffel_symbols(coordinates, base_metric)
    uplift_gamma = christoffel_symbols(uplift_coordinates, uplift)
    base_ricci = ricci_tensor(coordinates, base_metric)
    uplift_ricci = ricci_tensor(uplift_coordinates, uplift)
    emd = emd_residuals(coordinates, base_metric, scalar, potential, coupling)

    c1 = -1 / sp.sqrt(3)
    c2 = 2 / sp.sqrt(3)
    c3 = sp.S.One
    convention_residuals = (
        sp.simplify(c2 + 2 * c1),
        sp.simplify(c1**2 - sp.Rational(1, 3)),
        sp.simplify(sp.Rational(3, 2) * c2 - sp.sqrt(3)),
        sp.simplify(c3**2 - 1),
    )

    input_spec = {
        "source": {
            "kind": "constructed-exact-oracle",
            "provenance": "Minkowski metric in cylindrical coordinates with an exact local Kaluza gauge transform",
            "external_source": None,
        },
        "coordinates": [str(value) for value in uplift_coordinates],
        "base_metric": str(base_metric.tolist()),
        "scalar": str(scalar),
        "coupling": str(coupling),
        "gauge_function": str(gauge_function),
        "potential": [str(value) for value in potential],
        "uplift_ansatz": "exp(-phi/sqrt(3))*g + exp(2*phi/sqrt(3))*(dz+A)^2",
        "emd_convention": "docs/EMD_CONVENTION.md equations E1, E7 and scalar Euler-Lagrange equation",
        "expected_classification": "accepted-kaluza-vacuum-orbit",
    }

    checks = [
        {
            "name": "derived-uplift-constant-residuals-vanish",
            "passed": all(value == 0 for value in convention_residuals),
            "residual_sha256": _digest_expressions(convention_residuals),
        },
        {
            "name": "pure-gauge-field-strength-vanishes",
            "passed": matrix_is_zero(field),
            "residual_sha256": _digest_expressions(field),
        },
        {
            "name": "base-chart-is-nonlinear",
            "passed": any(
                sp.simplify(value) != 0
                for upper in base_gamma
                for lower_left in upper
                for value in lower_left
            ),
            "residual_sha256": _digest_expressions(
                value
                for upper in base_gamma
                for lower_left in upper
                for value in lower_left
            ),
        },
        {
            "name": "base-ricci-vanishes",
            "passed": matrix_is_zero(base_ricci),
            "residual_sha256": _digest_expressions(base_ricci),
        },
        {
            "name": "emd-residuals-vanish",
            "passed": emd.all_zero(),
            "residual_sha256": _digest_expressions(
                [
                    *list(emd.einstein),
                    *emd.maxwell,
                    emd.scalar,
                    *emd.bianchi.values(),
                ]
            ),
        },
        {
            "name": "uplift-equals-exact-coordinate-pullback",
            "passed": matrix_is_zero(uplift - pullback),
            "residual_sha256": _digest_expressions(uplift - pullback),
        },
        {
            "name": "uplift-chart-is-nonlinear",
            "passed": any(
                sp.simplify(value) != 0
                for upper in uplift_gamma
                for lower_left in upper
                for value in lower_left
            ),
            "residual_sha256": _digest_expressions(
                value
                for upper in uplift_gamma
                for lower_left in upper
                for value in lower_left
            ),
        },
        {
            "name": "uplift-ricci-vanishes",
            "passed": matrix_is_zero(uplift_ricci),
            "residual_sha256": _digest_expressions(uplift_ricci),
        },
    ]

    artifact = {
        "schema_version": SCHEMA_VERSION,
        "benchmark_id": BENCHMARK_ID,
        "evidence_class": "exact-symbolic-validation-not-lean-proof",
        "runtime": {
            "python": platform.python_version(),
            "sympy": sp.__version__,
        },
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
        failed = [
            check["name"] for check in artifact["checks"] if not check["passed"]
        ]
        raise SystemExit(f"benchmark failed: {', '.join(failed)}")

    destination = Path(__file__).parents[1] / "artifacts" / f"{BENCHMARK_ID}.json"
    rendered = json.dumps(artifact, indent=2, sort_keys=True) + "\n"
    if arguments.check:
        if not destination.exists():
            raise SystemExit(f"artifact is missing: {destination}")
        if destination.read_text(encoding="utf-8") != rendered:
            raise SystemExit(
                "artifact drift detected; regenerate and review " f"{destination}"
            )
    else:
        destination.write_text(rendered, encoding="utf-8")
    print(f"PASS {BENCHMARK_ID}: {len(artifact['checks'])} exact checks")
    print(f"{'VERIFIED' if arguments.check else 'WROTE'} {destination}")


if __name__ == "__main__":
    main()
