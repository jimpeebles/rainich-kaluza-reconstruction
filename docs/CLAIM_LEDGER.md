# Claim ledger

| ID | Claim | Current class | Status |
|---|---|---|---|
| RK-A1 | Non-null Maxwell stress satisfies a quadratic endomorphism identity | established input | literature-backed; conventions must be fixed |
| RK-A2 | `R = S + V` with rank-one scalar contribution in the selected EMD normalization | derivation obligation | abstract square-law implication formalized; derivation from convention-fixed EMD pending |
| RK-A2a | `S²=q²I` and `V²=tr(V)V` imply `RV+VR-tr(V)V=R²-q²I` for `R=S+V` | exact noncommutative algebra lemma | proved in Lean |
| RK-A3 | The Ricci characteristic polynomial has the proposed quadratic factorization | candidate exact theorem | coefficient consequences formalized; matrix derivation pending |
| RK-A4 | `C_KK = 0` is necessary on the generic branch | exact theorem target | algebraic consequence proved in Lean; geometric premise pending |
| RK-A5 | `C_KK = 0` is sufficient for a Kaluza interpretation | rejected overclaim | explicit Lean false positive; further rank, signature, differential, and field-equation conditions are required |
| RK-R1 | `q²` is recoverable from curvature when `R ≠ 0` | exact generic theorem target | coefficient formula proved in Lean |
| RK-R2a | The complementary eigenbasis block has forced diagonals and automatic trace compatibility | exact algebraic lemma | proved in Lean |
| RK-R2b | The forced block has a real rank-one completion iff `(a²-q²)(b²-q²)≤0` | exact algebraic lemma | proved in Lean |
| RK-R2c | The forced block factors as a Lorentzian scalar tensor iff its signature-adjusted diagonals are nonnegative | exact pointwise lemma | proved in Lean |
| RK-R2d | Nondegenerate scalar components generating the same mixed block are unique up to simultaneous sign | exact pointwise lemma | proved in Lean when one component is nonzero |
| RK-R2 | The full rank-one tensor `V` exists and is basis-independently unique on the generic Lorentzian branch | central open theorem | eigenbasis block existence and discrete uniqueness solved; basis-independent spectral assembly pending |
| RK-R3 | The reconstructed one-form is closed and locally equals `±dφ` | differential theorem target | unproved |
| RK-R4 | The residual tensor admits a Maxwell square root satisfying Maxwell equations | Rainich closure target | unproved |
| RK-R5 | The reconstructed fields satisfy the `a = √3` scalar equation | coupled closure target | unproved |
| RK-S1 | The conditions are necessary and sufficient on a generic local branch | Paper I goal | unproved |
| RK-D1 | `R = 0` branch | degenerate classification | open |
| RK-D2 | null Maxwell branch | degenerate classification | open |
| RK-D3 | null scalar-gradient branch | degenerate classification | open |
| RK-D4 | repeated/protected eigenvalue collisions | degenerate classification | open |
| RK-N1 | Exact Kaluza metrics pass all reconstructed conditions | reproducible computation | earlier evidence not yet imported |
| RK-N2 | Adversarial non-Kaluza metrics are rejected | selectivity study | open |

Every manuscript claim must cite one or more ledger IDs. Lean theorem names
should be added in a separate column once the geometric statements—not merely
their polynomial shadows—are formalized.
