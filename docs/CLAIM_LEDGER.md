# Claim ledger

| ID | Claim | Current class | Status |
|---|---|---|---|
| RK-A1 | Non-null Maxwell stress satisfies `S²=q²I` in the selected scaling | established input | convention and exact `q²` fixed; exterior-algebra derivation remains literature-backed |
| RK-A2 | `𝓡 = S + V`, `V=½v^♯⊗v`, and `tr(V)=R` in the selected EMD normalization | convention-fixed geometric derivation | derived from the cited EMD Einstein equation; rank-one square law proved basis-independently in Lean |
| RK-A2a | `S²=q²I` and `V²=tr(V)V` imply `RV+VR-tr(V)V=R²-q²I` for `R=S+V` | exact noncommutative algebra lemma | proved in Lean |
| RK-A2b | A rank-one perturbation retains an eigenvalue carried by a two-dimensional eigenspace; two Maxwell principal planes therefore protect a `±q` pair once their multiplicities are supplied | exact basis-independent linear-algebra theorem | proved in Lean by `exists_protected_eigenvector_of_pair` and `exists_protected_opposite_eigenvectors`; Maxwell principal-plane multiplicity remains a literature-backed geometric input |
| RK-A2c | A monic quartic with nonzero roots `+q` and `-q` necessarily has the factor `(x²-q²)`, with its complementary quadratic fixed by `e₁,e₂` | exact polynomial converse | proved in Lean by `monicQuartic_factorization_of_opposite_roots` and the coefficient-data equality theorem |
| RK-A3 | The Ricci characteristic polynomial has the proposed quadratic factorization | candidate geometric theorem | protected `±q` eigenvectors derived under principal-plane hypotheses and the root-to-factorization converse proved; formal Maxwell multiplicity and eigenvector-to-charpoly-root assembly remain pending |
| RK-A4 | `C_KK = 0` is necessary on the generic branch | exact theorem target | algebraic consequence proved in Lean; geometric premise pending |
| RK-A5 | `C_KK = 0` is sufficient for a Kaluza interpretation | rejected overclaim | explicit Lean false positive; further rank, signature, differential, and field-equation conditions are required |
| RK-R1 | `q²` is recoverable from curvature when `R ≠ 0` | exact generic theorem target | coefficient formula proved in Lean |
| RK-R2a | The complementary eigenbasis block has forced diagonals and automatic trace compatibility | exact algebraic lemma | proved in Lean |
| RK-R2b | The forced block has a real rank-one completion iff `(a²-q²)(b²-q²)≤0` | exact algebraic lemma | proved in Lean |
| RK-R2c | The forced block factors as a Lorentzian scalar tensor iff its signature-adjusted diagonals are nonnegative | exact pointwise lemma | proved in Lean |
| RK-R2c-a | The unsigned symmetric-completion and signature-aware scalar-factorization tests are incomparable on mixed-signature blocks | exact counterexample theorem and manuscript correction | both directions proved by `reconstructed_signature_unsigned_tests_incomparable` |
| RK-R2d | Nondegenerate scalar components generating the same mixed block are unique up to simultaneous sign | exact pointwise lemma | proved in Lean when one component is nonzero |
| RK-R2e | Any two scalar-generated generic block solutions are equal or related by the relative-sign spectral reflection | exact classification theorem | proved in Lean |
| RK-R2f | On the genuinely two-component branch, relative-sign partners are distinct while the reflection preserves the Ricci block | exact pointwise no-go theorem | proved in Lean |
| RK-R2 | Pointwise curvature uniquely determines the full rank-one tensor `V` on the generic branch | rejected overclaim | false on the two-component branch; only the orbit under the Ricci centralizer is determined |
| RK-R2g | The reconstruction equation is invariant under every involution commuting with `𝓡`; a commuting spectral idempotent canonically supplies such an involution | exact basis-independent algebra theorem | proved in Lean |
| RK-R2h | Both relative-sign covector branches can satisfy a linear closure condition only when their two spectral components satisfy it separately | exact differential-selection lemma | proved in Lean by `both_relativeSign_branches_closed_iff`; existence of a closed branch remains open |
| RK-R2i | On a two-root invariant block, `Pₐ=(R-bI)/(a-b)` is an idempotent Ricci-commuting spectral projector and acts correctly on the two eigenspaces | exact basis-independent polynomial theorem | proved in Lean by the `twoRootProjector_*` theorem family |
| RK-R3 | The reconstructed one-form is closed and locally equals `±dφ` | differential theorem target | unproved |
| RK-R4 | The residual tensor admits a Maxwell square root satisfying Maxwell equations | Rainich closure target | unproved |
| RK-R5 | The reconstructed fields satisfy the `a = √3` scalar equation | coupled closure target | unproved |
| RK-R5a | For `𝓕=exp(aφ/2)F`, the Bianchi/Maxwell equations become `d𝓕=(a/2)v∧𝓕` and `d*𝓕=-(a/2)v∧*𝓕`; a nonzero channel fixes signed `a`, while `a²` is invariant under scalar-orientation reversal | differential coupling target | form identities derived in `EMD_CONVENTION.md`; abstract uniqueness, probe recovery, and sign orbit proved in `DifferentialCoupling.lean`; curvature reconstruction open |
| RK-R5b | On a non-null differential channel, the Lorentzian pairing gives intrinsic formulas for `a` and `a²`, and the primal/dual values agree | exact evaluated-channel theorem | proved in `CouplingInvariant.lean`; construction of the paired forms from curvature remains open |
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
