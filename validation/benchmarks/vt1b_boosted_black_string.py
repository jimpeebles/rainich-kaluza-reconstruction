"""Convention-ladder benchmark: boosted Schwarzschild black-string reduction."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path
from typing import Iterable

import sympy as sp

from rk_validation.exact import (
    emd_residuals,
    exterior_derivative_one_form,
    exterior_derivative_two_form,
    hodge_star_two_form,
    kaluza_uplift_metric,
    matrix_is_zero,
    ricci_tensor,
    simplify_matrix,
    wedge_one_form_two_form,
)


SCHEMA_VERSION = 1
BENCHMARK_ID = "vt1b-boosted-black-string"


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest_expressions(expressions: Iterable[sp.Expr]) -> str:
    payload = "\n".join(sp.srepr(sp.simplify(expr)) for expr in expressions)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def build_artifact() -> dict[str, object]:
    t, r, theta, phi, z = sp.symbols("t r theta phi z", real=True)
    coordinates = (t, r, theta, phi)
    uplift_coordinates = (*coordinates, z)

    # Unit mass parameter and algebraic boost sinh(delta)=1, cosh(delta)=sqrt(2).
    f = 1 - 2 / r
    boost_sinh = sp.S.One
    boost_cosh = sp.sqrt(2)
    harmonic = 1 + (1 - f) * boost_sinh**2

    scalar = sp.sqrt(3) * sp.log(harmonic) / 2
    potential_t = (1 - f) * boost_sinh * boost_cosh / harmonic
    potential = (potential_t, sp.S.Zero, sp.S.Zero, sp.S.Zero)
    base_metric = sp.diag(
        -f / sp.sqrt(harmonic),
        sp.sqrt(harmonic) / f,
        sp.sqrt(harmonic) * r**2,
        sp.sqrt(harmonic) * r**2 * sp.sin(theta) ** 2,
    )
    coupling = sp.sqrt(3)

    field = exterior_derivative_one_form(coordinates, potential)
    scalar_gradient = tuple(sp.diff(scalar, coordinate) for coordinate in coordinates)

    # Exponentially rescale the physical field as calF=exp(a phi/2)F. The
    # curvature-normalized seed is calF/sqrt(2), but that constant cancels from
    # the differential coupling ratio. For this solution the exponential
    # factor is H^(3/4), so ``a`` is not inserted into the recovery formula.
    rainich_field = simplify_matrix(harmonic ** sp.Rational(3, 4) * field)
    volume_density = sp.sqrt(harmonic) * r**2 * sp.sin(theta)
    dual_rainich_field = hodge_star_two_form(
        base_metric, rainich_field, volume_density=volume_density
    )
    dual_derivative = exterior_derivative_two_form(
        coordinates, dual_rainich_field
    )
    dual_scalar_source = wedge_one_form_two_form(
        scalar_gradient, dual_rainich_field
    )
    recovered_couplings = tuple(
        sp.simplify(-2 * dual_derivative[index] / source)
        for index, source in dual_scalar_source.items()
        if sp.simplify(source) != 0
    )
    recovered_coupling_squares = tuple(
        sp.simplify(value**2) for value in recovered_couplings
    )
    uplift = kaluza_uplift_metric(base_metric, scalar, potential)

    # Pull back Schwarzschild_4 x R under
    # T = cosh(delta) t + sinh(delta) z,
    # Z = sinh(delta) t + cosh(delta) z.
    black_string = sp.diag(
        -f,
        1 / f,
        r**2,
        r**2 * sp.sin(theta) ** 2,
        1,
    )
    jacobian = sp.eye(5)
    jacobian[0, 0] = boost_cosh
    jacobian[0, 4] = boost_sinh
    jacobian[4, 0] = boost_sinh
    jacobian[4, 4] = boost_cosh
    pullback = simplify_matrix(jacobian.T * black_string * jacobian)

    base_ricci = ricci_tensor(coordinates, base_metric)
    uplift_ricci = ricci_tensor(uplift_coordinates, pullback)
    emd = emd_residuals(coordinates, base_metric, scalar, potential, coupling)

    inverse_base = simplify_matrix(base_metric.inv())
    mixed_ricci = simplify_matrix(inverse_base * base_ricci)
    # Newton identities give the characteristic coefficients without asking
    # SymPy to sort symbolic algebraic roots (which is both unnecessary and
    # brittle for expressions containing sqrt((r + 2) / r)).
    power_sums = {
        degree: sp.simplify(sp.trace(mixed_ricci**degree))
        for degree in range(1, 5)
    }
    p1, p2, p3, p4 = (power_sums[degree] for degree in range(1, 5))
    e1 = p1
    e2 = sp.simplify((p1**2 - p2) / 2)
    e3 = sp.simplify((p1**3 - 3 * p1 * p2 + 2 * p3) / 6)
    e4 = sp.simplify(
        (p1**4 - 6 * p1**2 * p2 + 3 * p2**2 + 8 * p1 * p3 - 6 * p4)
        / 24
    )
    kaluza_obstruction = sp.simplify(e1**2 * e4 - e1 * e2 * e3 + e3**2)
    off_diagonal_mixed_ricci = [
        mixed_ricci[row, column]
        for row in range(4)
        for column in range(4)
        if row != column
    ]
    repeated_angular_eigenvalue = sp.simplify(
        mixed_ricci[2, 2] - mixed_ricci[3, 3]
    )

    input_spec = {
        "source": {
            "kind": "constructed-from-standard-exact-solution",
            "provenance": "Lorentz boost of the direct product of four-dimensional Schwarzschild with a flat fifth direction",
            "external_source": None,
        },
        "coordinates": [str(value) for value in uplift_coordinates],
        "mass_parameter": "1",
        "boost": {"sinh_delta": "1", "cosh_delta": "sqrt(2)"},
        "base_metric": str(base_metric.tolist()),
        "scalar": str(scalar),
        "coupling": str(coupling),
        "potential": [str(value) for value in potential],
        "uplift_ansatz": "exp(-phi/sqrt(3))*g + exp(2*phi/sqrt(3))*(dz+A)^2",
        "expected_classification": "accepted-kaluza-emd-but-repeated-ricci-root",
    }

    checks = [
        {
            "name": "scalar-gradient-is-nonzero",
            "passed": any(sp.simplify(value) != 0 for value in scalar_gradient),
            "residual_sha256": _digest_expressions(scalar_gradient),
        },
        {
            "name": "maxwell-field-is-nonzero",
            "passed": not matrix_is_zero(field),
            "residual_sha256": _digest_expressions(field),
        },
        {
            "name": "base-ricci-is-nonzero",
            "passed": not matrix_is_zero(base_ricci),
            "residual_sha256": _digest_expressions(base_ricci),
        },
        {
            "name": "emd-residuals-vanish-at-sqrt-three",
            "passed": emd.all_zero(),
            "residual_sha256": _digest_expressions(
                [*list(emd.einstein), *emd.maxwell, emd.scalar, *emd.bianchi.values()]
            ),
        },
        {
            "name": "uplift-equals-boosted-black-string",
            "passed": matrix_is_zero(uplift - pullback),
            "residual_sha256": _digest_expressions(uplift - pullback),
        },
        {
            "name": "boosted-black-string-ricci-vanishes",
            "passed": matrix_is_zero(uplift_ricci),
            "residual_sha256": _digest_expressions(uplift_ricci),
        },
        {
            "name": "necessary-kaluza-polynomial-obstruction-vanishes",
            "passed": kaluza_obstruction == 0,
            "residual_sha256": _digest_expressions((kaluza_obstruction,)),
        },
        {
            "name": "dual-channel-reconstructs-coupling-squared-three",
            "passed": bool(recovered_coupling_squares)
            and all(value == 3 for value in recovered_coupling_squares),
            "residual_sha256": _digest_expressions(
                tuple(value - 3 for value in recovered_coupling_squares)
            ),
        },
        {
            "name": "ricci-spectrum-is-repeated-root-degenerate",
            "passed": all(
                sp.simplify(value) == 0 for value in off_diagonal_mixed_ricci
            )
            and repeated_angular_eigenvalue == 0,
            "residual_sha256": _digest_expressions(
                (*off_diagonal_mixed_ricci, repeated_angular_eigenvalue)
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
