# Paper I theorem-to-Lean map

This table prevents an informal manuscript statement from becoming stronger
than its machine-checked counterpart.

| Manuscript item | Lean declaration | Coverage |
|---|---|---|
| Quartic factorization expansion | `monicQuartic_fromFactorization` | complete coefficient algebra |
| Protected `±q` roots | `protected_positive_root`, `protected_negative_root` | complete polynomial statement |
| Candidate obstruction is necessary | `kaluzaObstruction_fromFactorization` | complete conditional on encoded factorization |
| Curvature formula for `q²` | `reconstructedQSq_fromFactorization` | complete for nonzero trace |
| Obstruction alone is insufficient | `algebraicFalsePositive_has_no_real_protected_pair` | complete explicit counterexample |
| Basis-independent rank-one square law | `rankOneEndomorphism_sq`, `rankOneEndomorphism_sq_eq_trace_smul` | complete for finite free real modules; no basis chosen |
| Coordinate-free reconstruction equation | `reconstructionEquation_of_decomposition`, `reconstructionEquation_of_eq_add` | complete in any associative real algebra, conditional on the two square laws |
| Centralizer invariance of reconstruction | `reconstructionEquation_conjugation_invariant` | complete for involutions commuting with the Ricci-like algebra element |
| Basis-independent spectral reflection | `reflectionOfIdempotent_sq`, `reflectionOfIdempotent_commutes`, `reconstructionEquation_reflectionOfIdempotent` | complete for commuting idempotents in any associative real algebra |
| Forced complementary diagonals | `reconstructedDiagonalA_solves`, `reconstructedDiagonalB_solves` | complete scalar component equations |
| Automatic trace compatibility | `reconstructedDiagonal_sum` | complete |
| Rank-one product identity | `reconstructedDiagonal_product` | complete |
| Real symmetric completion criterion | `exists_reconstructed_rankOne_completion_iff` | complete; not yet Lorentzian scalar factorization |
| Lorentzian scalar block determinant | `scalarMixedBlock_rankOne` | complete |
| Metric self-adjointness | `scalarMixedBlock_metric_selfAdjoint` | complete for signature signs squaring to one |
| Scalar-component uniqueness | `scalarMixedBlock_components_unique_up_to_sign` | complete up to simultaneous sign when the first component is nonzero |
| Signature-aware scalar factorization | `exists_scalar_components_iff` | complete for the two-dimensional mixed block |
| Generic reconstructed scalar block | `reconstructedBlock_has_scalar_factorization_iff` | complete pointwise diagonal criterion |
| Classification of all complementary Sylvester blocks | `solvesComplementaryBlock_iff` | complete for `a≠b`; resonant off-diagonals remain free |
| Existence of a scalar-generated complementary solution | `exists_scalarComplementaryBlock_iff` | complete signature-aware pointwise theorem |
| Classification into same/relative-sign blocks | `scalarComplementarySolutions_eq_or_flip` | complete for scalar-generated generic solutions |
| Distinct relative-sign counterpartner | `exists_distinct_relative_sign_solution` | complete when both components are nonzero |
| Reflection preserves Ricci and exchanges scalar blocks | `secondSpectralReflection_preserves_Ricci`, `secondSpectralReflection_conjugates` | complete two-dimensional centralizer realization |
| Convention-fixed EMD decomposition | `docs/EMD_CONVENTION.md`; `rankOneEndomorphism_sq_eq_trace_smul` | field-equation derivation documented; scalar square formalized; Maxwell square is a named literature input |
| Full tangent-space spectral assembly | — | open |
| Differential closure and local sufficiency | — | open |

The paper must not call the first five rows a geometric reconstruction theorem.
The public partial result is the generic existence/orbit classification and
pointwise uniqueness obstruction. The desired local reconstruction paper still
requires the final two open rows.
