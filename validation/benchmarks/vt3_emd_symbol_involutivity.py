"""Exact Cartan-symbol test for four-dimensional potential-form EMD.

This benchmark is deliberately narrower than a formal-integrability proof.
It certifies, by rational row reduction, that the displayed EMD principal
symbol has the expected Cartan characters, passes Cartan's first-prolongation
dimension test, and has the predicted growth through three prolongations.
It also verifies that the contracted-Bianchi and Maxwell-gauge identities
exhaust the corresponding symbol-level row dependencies.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path

import sympy as sp

from rk_validation.emd_symbol import (
    MINKOWSKI_DIAGONAL,
    cartan_characters,
    cartan_flag_dimensions,
    cartan_predicted_nullity,
    coordinate_formula_emd_principal_at_active_lower_jet,
    emd_gauge_amplitudes,
    emd_potential_sector,
    evaluated_covector_symbol,
    exact_rank,
    maxwell_sector,
    nullity,
    prolong_symbol,
    prolonged_first_syzygies,
    ricci_sector,
    scalar_sector,
    sparse_matrix_sha256,
    syzygies_annihilate_symbol,
    syzygies_exhaust_left_kernel,
)
from rk_validation.provenance import implementation_sha256


SCHEMA_VERSION = 1
BENCHMARK_ID = "vt3-emd-symbol-involutivity"

EXPECTED_SECTORS = {
    "linearized-Ricci": {
        "flag_dimensions": (90, 50, 20, 4, 0),
        "cartan_characters": (40, 30, 16, 4),
        "nullities": (90, 164, 266, 400),
        "ranks": (10, 36, 84, 160),
    },
    "Maxwell-potential": {
        "flag_dimensions": (36, 20, 8, 1, 0),
        "cartan_characters": (16, 12, 7, 1),
        "nullities": (36, 65, 104, 154),
        "ranks": (4, 15, 36, 70),
    },
    "scalar-wave": {
        "flag_dimensions": (9, 5, 2, 0, 0),
        "cartan_characters": (4, 3, 2, 0),
        "nullities": (9, 16, 25, 36),
        "ranks": (1, 4, 10, 20),
    },
    "EMD-potential": {
        "flag_dimensions": (135, 75, 30, 5, 0),
        "cartan_characters": (60, 45, 25, 5),
        "nullities": (135, 245, 395, 590),
        "ranks": (15, 55, 130, 250),
    },
}


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _sector_record(sector: object) -> dict[str, object]:
    symbols = tuple(prolong_symbol(sector, degree) for degree in range(4))
    dimensions = cartan_flag_dimensions(sector)
    characters = cartan_characters(sector)
    prolongations = []
    for degree, symbol in enumerate(symbols):
        rank = exact_rank(symbol.matrix)
        prolongations.append(
            {
                "jet_order": symbol.jet_order,
                "matrix_shape": list(symbol.matrix.shape),
                "nonzero_entries": len(symbol.matrix.todok()),
                "rank": rank,
                "nullity": symbol.matrix.cols - rank,
                "cartan_predicted_nullity": cartan_predicted_nullity(
                    characters, degree
                ),
                "matrix_sha256": sparse_matrix_sha256(symbol.matrix),
            }
        )
    syzygies = []
    for degree in range(1, 4):
        relations = prolonged_first_syzygies(sector, degree)
        symbol = symbols[degree].matrix
        relation_rank = exact_rank(relations)
        syzygies.append(
            {
                "jet_order": 2 + degree,
                "relation_matrix_shape": list(relations.shape),
                "relation_rank": relation_rank,
                "symbol_left_nullity": symbol.rows - exact_rank(symbol),
                "annihilates_symbol": syzygies_annihilate_symbol(sector, degree),
                "exhausts_left_kernel": syzygies_exhaust_left_kernel(
                    sector, degree
                ),
                "matrix_sha256": sparse_matrix_sha256(relations),
            }
        )
    return {
        "field_count": len(sector.fields),
        "equation_count": len(sector.equations),
        "standard_flag_dimensions": list(dimensions),
        "cartan_characters": list(characters),
        "prolongations": prolongations,
        "differential_syzygies": syzygies,
    }


def build_artifact() -> dict[str, object]:
    ricci = ricci_sector()
    maxwell = maxwell_sector()
    scalar = scalar_sector()
    emd = emd_potential_sector()
    sectors = (ricci, maxwell, scalar, emd)
    records = {sector.name: _sector_record(sector) for sector in sectors}
    coordinate_extracted_principal = (
        coordinate_formula_emd_principal_at_active_lower_jet()
    )

    expected_sector_checks = []
    for sector in sectors:
        expected = EXPECTED_SECTORS[sector.name]
        record = records[sector.name]
        expected_sector_checks.append(
            record["standard_flag_dimensions"]
            == list(expected["flag_dimensions"])
            and record["cartan_characters"]
            == list(expected["cartan_characters"])
            and tuple(
                prolongation["nullity"]
                for prolongation in record["prolongations"]
            )
            == expected["nullities"]
            and tuple(
                prolongation["rank"]
                for prolongation in record["prolongations"]
            )
            == expected["ranks"]
        )

    combined_characters = cartan_characters(emd)
    combined_prolongations = tuple(prolong_symbol(emd, degree) for degree in range(4))
    sector_prolongations = {
        sector.name: tuple(prolong_symbol(sector, degree) for degree in range(4))
        for sector in (ricci, maxwell, scalar)
    }
    direct_sum_matches = all(
        exact_rank(combined_prolongations[degree].matrix)
        == sum(
            exact_rank(sector_prolongations[sector.name][degree].matrix)
            for sector in (ricci, maxwell, scalar)
        )
        and nullity(combined_prolongations[degree].matrix)
        == sum(
            nullity(sector_prolongations[sector.name][degree].matrix)
            for sector in (ricci, maxwell, scalar)
        )
        for degree in range(4)
    )

    spacelike = evaluated_covector_symbol(emd, (0, 0, 0, 1))
    timelike = evaluated_covector_symbol(emd, (1, 0, 0, 0))
    null = evaluated_covector_symbol(emd, (1, 0, 0, 1))
    mixed_spacelike = evaluated_covector_symbol(emd, (1, 2, 3, 5))
    mixed_timelike = evaluated_covector_symbol(emd, (5, 1, 2, 3))
    mixed_null = evaluated_covector_symbol(emd, (5, 3, 4, 0))
    spacelike_gauge = emd_gauge_amplitudes((0, 0, 0, 1))
    timelike_gauge = emd_gauge_amplitudes((1, 0, 0, 0))
    null_gauge = emd_gauge_amplitudes((1, 0, 0, 1))
    mixed_spacelike_gauge = emd_gauge_amplitudes((1, 2, 3, 5))
    mixed_timelike_gauge = emd_gauge_amplitudes((5, 1, 2, 3))
    mixed_null_gauge = emd_gauge_amplitudes((5, 3, 4, 0))
    polarization_data = {}
    for sector in (ricci, maxwell, scalar):
        nonnull_sector_symbol = evaluated_covector_symbol(
            sector, (1, 2, 3, 5)
        )
        null_sector_symbol = evaluated_covector_symbol(sector, (5, 3, 4, 0))
        nonnull_kernel = nullity(nonnull_sector_symbol)
        null_kernel = nullity(null_sector_symbol)
        polarization_data[sector.name] = {
            "nonnull_kernel_dimension": nonnull_kernel,
            "null_kernel_dimension": null_kernel,
            "null_excess_beyond_gauge": null_kernel - nonnull_kernel,
            "nonnull_matrix_sha256": sparse_matrix_sha256(
                nonnull_sector_symbol
            ),
            "null_matrix_sha256": sparse_matrix_sha256(null_sector_symbol),
        }
    covector_data = {
        "spacelike-e3": {
            "lorentz_square": 1,
            "rank": exact_rank(spacelike),
            "kernel_dimension": nullity(spacelike),
            "gauge_image_dimension": exact_rank(spacelike_gauge),
            "gauge_image_annihilated": not (spacelike * spacelike_gauge).todok(),
            "matrix_sha256": sparse_matrix_sha256(spacelike),
        },
        "timelike-e0": {
            "lorentz_square": -1,
            "rank": exact_rank(timelike),
            "kernel_dimension": nullity(timelike),
            "gauge_image_dimension": exact_rank(timelike_gauge),
            "gauge_image_annihilated": not (timelike * timelike_gauge).todok(),
            "matrix_sha256": sparse_matrix_sha256(timelike),
        },
        "null-e0-plus-e3": {
            "lorentz_square": 0,
            "rank": exact_rank(null),
            "kernel_dimension": nullity(null),
            "gauge_image_dimension": exact_rank(null_gauge),
            "gauge_image_annihilated": not (null * null_gauge).todok(),
            "matrix_sha256": sparse_matrix_sha256(null),
        },
        "mixed-spacelike-1-2-3-5": {
            "lorentz_square": 37,
            "rank": exact_rank(mixed_spacelike),
            "kernel_dimension": nullity(mixed_spacelike),
            "gauge_image_dimension": exact_rank(mixed_spacelike_gauge),
            "gauge_image_annihilated": not (
                mixed_spacelike * mixed_spacelike_gauge
            ).todok(),
            "matrix_sha256": sparse_matrix_sha256(mixed_spacelike),
        },
        "mixed-timelike-5-1-2-3": {
            "lorentz_square": -11,
            "rank": exact_rank(mixed_timelike),
            "kernel_dimension": nullity(mixed_timelike),
            "gauge_image_dimension": exact_rank(mixed_timelike_gauge),
            "gauge_image_annihilated": not (
                mixed_timelike * mixed_timelike_gauge
            ).todok(),
            "matrix_sha256": sparse_matrix_sha256(mixed_timelike),
        },
        "mixed-null-5-3-4-0": {
            "lorentz_square": 0,
            "rank": exact_rank(mixed_null),
            "kernel_dimension": nullity(mixed_null),
            "gauge_image_dimension": exact_rank(mixed_null_gauge),
            "gauge_image_annihilated": not (mixed_null * mixed_null_gauge).todok(),
            "matrix_sha256": sparse_matrix_sha256(mixed_null),
        },
    }

    input_spec = {
        "dimension": 4,
        "point_metric": list(MINKOWSKI_DIAGONAL),
        "coordinate_condition": "normal-coordinate point, so first metric jet vanishes",
        "active_witness_scalar_value": "phi=0",
        "active_witness_first_jet": {
            "dphi": [1, 0, 2, 0],
            "physical_F_nonzero_components": {
                "F01": "sqrt(2)",
                "F23": "sqrt(2)",
            },
            "radial_gauge_potential": ["0", "sqrt(2)*x0", "0", "sqrt(2)*x2"],
            "coupling_for_coordinate_extraction": "symbolic real a",
        },
        "unknowns": {
            "symmetric_metric_components": 10,
            "potential_components": 4,
            "scalar_components": 1,
        },
        "equations": {
            "trace_reversed_Ricci_components": 10,
            "weighted_Maxwell_potential_components": 4,
            "scalar_wave_components": 1,
        },
        "principal_symbol_scope": (
            "Matter, exponential-coupling, and active-witness values occur only "
            "below order two; the symbol is Ricci direct-sum div-d direct-sum wave"
        ),
        "rank_arithmetic": "exact rational DomainMatrix row reduction",
        "standard_flag": [
            "span(e0)",
            "span(e0,e1)",
            "span(e0,e1,e2)",
            "span(e0,e1,e2,e3)",
        ],
        "falsification_targets": {
            "EMD_cartan_characters": [60, 45, 25, 5],
            "dim_g2": 135,
            "dim_g3": 245,
        },
    }

    checks = [
        {
            "name": "sector-ranks-flags-and-characters-match-falsification-targets",
            "passed": all(expected_sector_checks),
        },
        {
            "name": "emd-order-two-symbol-is-surjective",
            "passed": exact_rank(emd.principal) == 15
            and emd.principal.shape == (15, 150),
        },
        {
            "name": "full-coordinate-emd-evaluator-reproduces-symbol-at-active-lower-jet",
            "passed": coordinate_extracted_principal == emd.principal
            and exact_rank(coordinate_extracted_principal) == 15,
        },
        {
            "name": "emd-g2-and-g3-have-target-dimensions",
            "passed": nullity(combined_prolongations[0].matrix) == 135
            and nullity(combined_prolongations[1].matrix) == 245,
        },
        {
            "name": "emd-symbol-passes-cartans-first-prolongation-dimension-test",
            "passed": nullity(combined_prolongations[1].matrix)
            == sum(
                (index + 1) * character
                for index, character in enumerate(combined_characters)
            ),
        },
        {
            "name": "cartan-hilbert-growth-persists-through-g4-and-g5",
            "passed": all(
                nullity(symbol.matrix)
                == cartan_predicted_nullity(combined_characters, degree)
                for degree, symbol in enumerate(combined_prolongations)
            ),
        },
        {
            "name": "bianchi-and-maxwell-syzygies-annihilate-first-three-prolongations",
            "passed": all(
                syzygies_annihilate_symbol(emd, degree)
                for degree in range(1, 4)
            ),
        },
        {
            "name": "known-syzygies-exhaust-first-three-symbol-left-kernels",
            "passed": all(
                syzygies_exhaust_left_kernel(emd, degree)
                for degree in range(1, 4)
            ),
        },
        {
            "name": "emd-prolongations-are-sectorwise-direct-sums",
            "passed": direct_sum_matches,
        },
        {
            "name": "non-null-covectors-have-only-five-gauge-kernel-directions",
            "passed": exact_rank(spacelike) == 10
            and nullity(spacelike) == 5
            and exact_rank(spacelike_gauge) == 5
            and not (spacelike * spacelike_gauge).todok()
            and exact_rank(timelike) == 10
            and nullity(timelike) == 5
            and exact_rank(timelike_gauge) == 5
            and not (timelike * timelike_gauge).todok()
            and exact_rank(mixed_spacelike) == 10
            and nullity(mixed_spacelike) == 5
            and exact_rank(mixed_spacelike_gauge) == 5
            and not (mixed_spacelike * mixed_spacelike_gauge).todok()
            and exact_rank(mixed_timelike) == 10
            and nullity(mixed_timelike) == 5
            and exact_rank(mixed_timelike_gauge) == 5
            and not (mixed_timelike * mixed_timelike_gauge).todok(),
        },
        {
            "name": "null-covector-is-characteristic-beyond-gauge",
            "passed": exact_rank(null) == 5
            and nullity(null) == 10
            and exact_rank(null_gauge) == 5
            and not (null * null_gauge).todok()
            and exact_rank(mixed_null) == 5
            and nullity(mixed_null) == 10
            and exact_rank(mixed_null_gauge) == 5
            and not (mixed_null * mixed_null_gauge).todok(),
        },
        {
            "name": "null-symbol-excess-splits-into-two-plus-two-plus-one-modes",
            "passed": polarization_data["linearized-Ricci"][
                "null_excess_beyond_gauge"
            ]
            == 2
            and polarization_data["Maxwell-potential"][
                "null_excess_beyond_gauge"
            ]
            == 2
            and polarization_data["scalar-wave"][
                "null_excess_beyond_gauge"
            ]
            == 1,
        },
    ]

    matrix_hash_manifest = {
        sector_name: [
            prolongation["matrix_sha256"]
            for prolongation in record["prolongations"]
        ]
        for sector_name, record in records.items()
    }
    model_sha256 = hashlib.sha256(
        _canonical_json(matrix_hash_manifest).encode("utf-8")
    ).hexdigest()
    artifact = {
        "schema_version": SCHEMA_VERSION,
        "benchmark_id": BENCHMARK_ID,
        "evidence_class": "exact-rational-symbol-certificate-not-formal-integrability-proof",
        "runtime": {"python": platform.python_version(), "sympy": sp.__version__},
        "input": input_spec,
        "input_sha256": hashlib.sha256(
            _canonical_json(input_spec).encode("utf-8")
        ).hexdigest(),
        "model_sha256": model_sha256,
        "implementation_sha256": implementation_sha256(
            (
                "rk_validation/emd_symbol.py",
                "rk_validation/exact.py",
                "benchmarks/vt3_emd_symbol_involutivity.py",
            )
        ),
        "coordinate_formula_cross_check": {
            "matrix_shape": list(coordinate_extracted_principal.shape),
            "rank": exact_rank(coordinate_extracted_principal),
            "matches_index_formula": coordinate_extracted_principal == emd.principal,
            "matrix_sha256": sparse_matrix_sha256(coordinate_extracted_principal),
            "regularity_consequence": (
                "the coordinate equation map is a submersion in its 150 "
                "highest-jet directions at the displayed active lower jet"
            ),
        },
        "characteristic_polarization_count": polarization_data,
        "sectors": records,
        "covector_symbols": covector_data,
        "checks": checks,
        "passed": all(bool(check["passed"]) for check in checks),
        "interpretation": {
            "certified": (
                "the displayed rational principal symbol has Cartan characters "
                "(60,45,25,5), dim(g2)=135, dim(g3)=245, and involutive "
                "Cartan/Hilbert growth through g5; the five standard first "
                "syzygies exhaust the tested symbol-level dependencies; and "
                "the full coordinate EMD residual evaluator has this same "
                "surjective highest-jet Jacobian at the active lower jet; "
                "the null-symbol kernel modulo gauge splits into 2 metric, "
                "2 Maxwell, and 1 scalar amplitudes"
            ),
            "not_certified": (
                "an independent derivation from the variational action; the "
                "off-shell lower-order Noether compatibility; regularity of "
                "every prolonged nonlinear equation manifold; all-order "
                "formal integrability; or analytic solution-germ realization"
            ),
        },
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
