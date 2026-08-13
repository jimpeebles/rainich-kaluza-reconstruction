"""Negative convention ladder: an exact a^2=1 dilatonic black hole."""

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
BENCHMARK_ID = "vt1c-non-kaluza-dilaton"


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest_expressions(expressions: Iterable[sp.Expr]) -> str:
    payload = "\n".join(sp.srepr(sp.simplify(expr)) for expr in expressions)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def build_artifact() -> dict[str, object]:
    t, r, theta, phi, z = sp.symbols("t r theta phi z", real=True)
    coordinates = (t, r, theta, phi)
    uplift_coordinates = (*coordinates, z)

    # Gibbons--Maeda--Garfinkle--Horowitz--Strominger electric solution with
    # r_+=2, r_-=1 and Q=1.  The repository normalization is obtained from the
    # common action R-2(dϕ)^2-exp(-2ϕ)F_std^2 by
    # phi=-2ϕ, A=2 A_std and a=1.
    lapse = 1 - 2 / r
    dilaton_factor = 1 - 1 / r
    scalar = -sp.log(dilaton_factor)
    coupling = sp.S.One
    potential = (2 / r, sp.S.Zero, sp.S.Zero, sp.S.Zero)
    base_metric = sp.diag(
        -lapse,
        1 / lapse,
        r**2 * dilaton_factor,
        r**2 * dilaton_factor * sp.sin(theta) ** 2,
    )

    field = exterior_derivative_one_form(coordinates, potential)
    scalar_gradient = tuple(sp.diff(scalar, coordinate) for coordinate in coordinates)
    rainich_field = simplify_matrix(
        dilaton_factor ** sp.Rational(-1, 2) * field
    )
    volume_density = r**2 * dilaton_factor * sp.sin(theta)
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

    base_ricci = ricci_tensor(coordinates, base_metric)
    emd = emd_residuals(coordinates, base_metric, scalar, potential, coupling)
    uplift = kaluza_uplift_metric(base_metric, scalar, potential)
    uplift_ricci = ricci_tensor(uplift_coordinates, uplift)

    inverse_base = simplify_matrix(base_metric.inv())
    mixed_ricci = simplify_matrix(inverse_base * base_ricci)
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
            "kind": "published-exact-solution-with-explicit-convention-map",
            "provenance": "Gibbons--Maeda / Garfinkle--Horowitz--Strominger static electric dilaton black hole",
            "external_source": "https://doi.org/10.1103/PhysRevD.43.3140",
        },
        "coordinates": [str(value) for value in uplift_coordinates],
        "parameters": {"r_plus": "2", "r_minus": "1", "standard_charge": "1"},
        "convention_map": "phi=-2*standard_phi; A=2*standard_A; a=1",
        "base_metric": str(base_metric.tolist()),
        "scalar": str(scalar),
        "coupling": str(coupling),
        "potential": [str(value) for value in potential],
        "expected_classification": "valid-emd-with-a-squared-one-but-rejected-as-kaluza-and-repeated-root",
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
            "name": "emd-residuals-vanish-at-coupling-one",
            "passed": emd.all_zero(),
            "residual_sha256": _digest_expressions(
                [*list(emd.einstein), *emd.maxwell, emd.scalar, *emd.bianchi.values()]
            ),
        },
        {
            "name": "dual-channel-reconstructs-coupling-squared-one",
            "passed": bool(recovered_coupling_squares)
            and all(value == 1 for value in recovered_coupling_squares),
            "residual_sha256": _digest_expressions(
                tuple(value - 1 for value in recovered_coupling_squares)
            ),
        },
        {
            "name": "kaluza-coupling-selector-rejects",
            "passed": bool(recovered_coupling_squares)
            and all(value != 3 for value in recovered_coupling_squares),
            "residual_sha256": _digest_expressions(
                tuple(value - 3 for value in recovered_coupling_squares)
            ),
        },
        {
            "name": "necessary-algebraic-obstruction-still-vanishes",
            "passed": kaluza_obstruction == 0,
            "residual_sha256": _digest_expressions((kaluza_obstruction,)),
        },
        {
            "name": "convention-kaluza-uplift-is-not-ricci-flat",
            "passed": not matrix_is_zero(uplift_ricci),
            "residual_sha256": _digest_expressions(uplift_ricci),
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
