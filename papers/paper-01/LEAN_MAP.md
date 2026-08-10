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
| Coordinate-free reconstruction equation | `reconstructionEquation_of_decomposition`, `reconstructionEquation_of_eq_add` | complete in any associative real algebra, conditional on the two square laws |
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
| Derivation of the square-law premises from convention-fixed EMD | — | open geometric step |
| Basis-independent generic reconstruction | — | open |
| Differential closure and local sufficiency | — | open |

The paper must not call the first five rows a geometric reconstruction theorem.
The publishable algebraic result begins with the forced block classification,
and the desired main paper requires the final three open rows.
