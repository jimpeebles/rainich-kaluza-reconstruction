"""Exact regression tests for the potential-form EMD symbol certificate."""

from __future__ import annotations

import json
from pathlib import Path
import unittest

from benchmarks.vt3_emd_symbol_involutivity import build_artifact
from rk_validation.emd_symbol import (
    cartan_characters,
    cartan_flag_dimensions,
    coordinate_formula_emd_principal_at_active_lower_jet,
    emd_gauge_amplitudes,
    emd_potential_sector,
    evaluated_covector_symbol,
    exact_rank,
    nullity,
    prolong_symbol,
    syzygies_exhaust_left_kernel,
)


class EMDPotentialSymbolTests(unittest.TestCase):
    def test_exact_cartan_target_and_first_prolongation(self) -> None:
        emd = emd_potential_sector()
        self.assertEqual(cartan_flag_dimensions(emd), (135, 75, 30, 5, 0))
        self.assertEqual(cartan_characters(emd), (60, 45, 25, 5))
        self.assertEqual(nullity(prolong_symbol(emd, 0).matrix), 135)
        self.assertEqual(nullity(prolong_symbol(emd, 1).matrix), 245)

    def test_known_identities_exhaust_tested_left_kernels(self) -> None:
        emd = emd_potential_sector()
        for degree in range(1, 4):
            with self.subTest(jet_order=2 + degree):
                self.assertTrue(syzygies_exhaust_left_kernel(emd, degree))

    def test_full_coordinate_evaluator_gives_same_active_symbol(self) -> None:
        emd = emd_potential_sector()
        extracted = coordinate_formula_emd_principal_at_active_lower_jet()
        self.assertEqual(extracted, emd.principal)
        self.assertEqual(exact_rank(extracted), 15)

    def test_non_null_kernel_equals_explicit_gauge_image(self) -> None:
        emd = emd_potential_sector()
        for covector in (
            (1, 0, 0, 0),
            (0, 0, 0, 1),
            (1, 2, 3, 5),
            (5, 1, 2, 3),
        ):
            with self.subTest(covector=covector):
                symbol = evaluated_covector_symbol(emd, covector)
                gauge = emd_gauge_amplitudes(covector)
                self.assertEqual(nullity(symbol), 5)
                self.assertEqual(exact_rank(gauge), 5)
                self.assertFalse((symbol * gauge).todok())

    def test_committed_artifact_is_exactly_reproducible(self) -> None:
        artifact = build_artifact()
        destination = (
            Path(__file__).parents[1]
            / "artifacts"
            / "vt3-emd-symbol-involutivity.json"
        )
        committed = json.loads(destination.read_text(encoding="utf-8"))
        self.assertEqual(committed, artifact)
        self.assertTrue(artifact["passed"])
        self.assertEqual(len(artifact["checks"]), 12)
        self.assertEqual(
            {
                sector: data["null_excess_beyond_gauge"]
                for sector, data in artifact[
                    "characteristic_polarization_count"
                ].items()
            },
            {
                "linearized-Ricci": 2,
                "Maxwell-potential": 2,
                "scalar-wave": 1,
            },
        )


if __name__ == "__main__":
    unittest.main()
