"""Generic adversarial oracle: second-jet perturbation of the helical solution."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path
from typing import Iterable

import sympy as sp

from rk_validation.exact import emd_residuals_at, matrix_is_zero, ricci_tensor_at, simplify_matrix


SCHEMA_VERSION = 1
BENCHMARK_ID = "vt2b-generic-near-miss"


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest_expressions(expressions: Iterable[sp.Expr]) -> str:
    payload = "\n".join(sp.srepr(sp.simplify(expr)) for expr in expressions)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def build_artifact() -> dict[str, object]:
    t, r, theta, phi, z = sp.symbols("t r theta phi z", real=True)
    coordinates = (t, r, theta, phi)
    point = {t: sp.S.Zero, r: sp.S(3), theta: sp.pi / 4, phi: sp.S.Zero}

    lapse = 1 - 2 / r
    black_string = sp.diag(
        -lapse,
        1 / lapse,
        r**2,
        r**2 * sp.sin(theta) ** 2,
        1,
    )
    jacobian = sp.eye(5)
    jacobian[0, 0] = sp.sqrt(2)
    jacobian[0, 4] = 1
    jacobian[3, 4] = 1
    jacobian[4, 0] = 1
    jacobian[4, 4] = sp.sqrt(2)
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
    positive_metric = simplify_matrix(sp.sqrt(fiber_norm) * horizontal_metric)

    # Change only the tt second jet at the exact point.  The value and first
    # jet agree with the genuine Kaluza metric, so this is a deliberately close
    # adversary rather than an obviously unrelated metric.
    perturbation = sp.Rational(1, 100) * (r - 3) ** 2
    near_miss_mutable = sp.MutableDenseMatrix(positive_metric)
    near_miss_mutable[0, 0] += perturbation
    near_miss_metric = sp.ImmutableMatrix(near_miss_mutable)

    perturbation_value = sp.simplify(perturbation.subs(point))
    perturbation_first = tuple(
        sp.simplify(sp.diff(perturbation, coordinate).subs(point))
        for coordinate in coordinates
    )
    perturbation_second_rr = sp.simplify(sp.diff(perturbation, r, r).subs(point))

    point_metric = simplify_matrix(near_miss_metric.subs(point))
    point_ricci = ricci_tensor_at(coordinates, near_miss_metric, point)
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
    kaluza_obstruction = sp.factor(e1**2 * e4 - e1 * e2 * e3 + e3**2)
    emd = emd_residuals_at(
        coordinates,
        near_miss_metric,
        scalar,
        potential,
        sp.sqrt(3),
        point,
    )

    input_spec = {
        "source": {
            "kind": "adversarial-exact-second-jet-perturbation",
            "provenance": "tt component of vt2-generic-helical-string shifted by (r-3)^2/100",
            "external_source": None,
        },
        "coordinates": [str(value) for value in (*coordinates, z)],
        "exact_point": {str(key): str(value) for key, value in point.items()},
        "perturbation": str(perturbation),
        "expected_classification": "generic-non-emd-rejected-by-kaluza-polynomial-obstruction",
    }

    checks = [
        {
            "name": "perturbation-value-and-first-jet-vanish",
            "passed": perturbation_value == 0
            and all(value == 0 for value in perturbation_first),
            "residual_sha256": _digest_expressions(
                (perturbation_value, *perturbation_first)
            ),
        },
        {
            "name": "perturbation-second-jet-is-nonzero",
            "passed": perturbation_second_rr != 0,
            "residual_sha256": _digest_expressions((perturbation_second_rr,)),
        },
        {
            "name": "point-metric-remains-lorentzian",
            "passed": bool(sp.simplify(point_metric.det()) < 0),
            "residual_sha256": _digest_expressions((point_metric.det(),)),
        },
        {
            "name": "mixed-ricci-spectrum-remains-real-and-simple",
            "passed": len(eigenvalues) == 4
            and all(multiplicity == 1 for multiplicity in eigenvalues.values())
            and all(value.is_real is True for value in eigenvalues),
            "residual_sha256": _digest_expressions(eigenvalues.keys()),
        },
        {
            "name": "characteristic-discriminant-remains-nonzero",
            "passed": characteristic_discriminant != 0,
            "residual_sha256": _digest_expressions((characteristic_discriminant,)),
        },
        {
            "name": "kaluza-polynomial-obstruction-is-nonzero",
            "passed": kaluza_obstruction != 0,
            "residual_sha256": _digest_expressions((kaluza_obstruction,)),
        },
        {
            "name": "original-emd-fields-no-longer-solve-equations",
            "passed": not emd.all_zero() and not matrix_is_zero(emd.einstein),
            "residual_sha256": _digest_expressions(
                [*list(emd.einstein), *emd.maxwell, emd.scalar, *emd.bianchi.values()]
            ),
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
