# Claim ledger

Date: 2026-08-13

Status: canonical proved/external/open boundary for the active paper

Evidence labels:

- **Lean** -- compiled theorem in this repository and intended for the axiom
  audit.
- **Human + external** -- a written mathematical argument using a cited
  theorem, not formalized in Lean.
- **Exact symbolic** -- reproducible validation evidence, not a theorem.
- **Open** -- not available for use as a conclusion.

## Headline claims

| ID | Claim | Evidence | Exact boundary |
|---|---|---|---|
| C1 | When the canonical seed amplitude and scalar covector are nonzero, the fibers of the complete first curvature-seed channel map are exactly the free affine real-shear orbits: equal channels iff \(A'=A\) and \((\omega',B')\) differs from \((\omega,B)\) by a unique shear. | **Lean**: `canonicalFullComplexionCouplingChannels_eq_iff_shearOrbit`, `canonicalFirstOrderChannelShear_parameter_unique` | Exact complete-channel fiber classification; still not a solution-level metric-jet theorem by itself. |
| C2 | One fixed active formal metric three-jet supports the displayed truncated EMD data for every real \(a\), with both the rescaled and correctly unweighted physical Maxwell first jets injective in \(a\). | **Lean**: `activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling`, `activeAmbiguityMaxwellFirstJet_injective`, `activeAmbiguityPhysicalMaxwellFirstJet_component`, `activeAmbiguityPhysicalMaxwellFirstJet_injective` | Finite-jet statement. |
| C3 | The common Ricci source has four distinct real eigenvalues and the activity wedge is nonzero. | **Lean**: `activeAmbiguityRicciSource_has_four_distinct_real_eigenpairs`, `activeAmbiguityPhysicalComplexion_wedge_component` | Simple-spectrum and active at the marked point; no density claim.  First Bianchi compatibility follows in the human realization argument from the fully symmetric metric three-jet and its proved Ricci first prolongation. |
| C4 | The common metric data are realized by an actual polynomial metric germ through order three, and the active family's correctly unweighted closed physical Maxwell one-jet has explicit compatible radial-gauge potential two-jet coefficients for every \(a\). | **Lean**: `activeAmbiguityPolynomialMetricGerm_realizes_threeJet`, `matrixExteriorDerivative_activeAmbiguityPhysicalMaxwellFirstJet`, `activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes` | The metric is an actual field with genuine Fréchet derivatives. The potential theorem presently constructs holonomic coefficient arrays, not an actual quadratic one-form field; neither result alone is an all-order EMD solution. The family-specific theorem, rather than the generic conditional radial formula alone, supplies the closure premise. |
| C5 | Conditional on the explicit analytic EMD involutivity lemma, for every real \(a\) the finite collision extends to a local real-analytic EMD solution germ in pure second-order potential variables \((g,A,\phi)\). | **Human + external**: extension of Kruglikov Theorem 3 by the determined scalar-wave block of Lemma 4, EMD Noether/Bianchi identity, and Cartan--Kähler; proof in `ANALYTIC_EMD_REALIZATION.md` | The finite-jet and gauge completion is closed.  Kruglikov does not state the EMD involutivity lemma verbatim; it remains the single specialist-audit dependency and is not formalized in Lean. |
| C6 | Under C5's explicit involutivity lemma, no function of the metric three-jet identifies \(a^2\) on the analytic family; in particular \(a=\sqrt3\) and \(a=1\) collide. | **Human corollary** of C2--C5 | Equality is in one fixed normal-coordinate chart, which suffices for impossibility.  No common metric four-jet or closed-form spacetime is claimed. |
| C7 | On \(\eta\wedge Jv\ne0\), the next-order constancy equation uniquely recovers \(B\), component independently, and returns \(a^2=A^2+B^2\).  On the explicit active formal family, fixed fourth-order outputs for \(a,b\) agree iff \(a=\pm b\). | **Lean**: `couplingSqFromNextOrderComponent_eq`, `fourthOrderCouplingSqCandidate_eq_physical`, `activeAmbiguityFourthOrderCouplingSqCandidates_eq_iff`, and uniqueness/confluence families | Physical curvature channel.  The iff theorem is for the explicit finite-jet family, not an all-order PDE theorem.  The surviving sign is the scalar-orientation/coupling-sign symmetry observed throughout the paper; no new all-order symmetry theorem is being claimed. |
| C8 | A finite metric-only coordinate detector whose nested Fréchet-derivative definitions reach metric order four searches exactly \(6{,}291{,}456\) raw choices and has an accepted choice returning physical \(a^2\) on the packaged active-regular Ricci--exterior EMD locus. | **Lean**: `allActualMetricDetectorChoices4_card`, `exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD`, and physical-active wrappers | The order statement is currently dependency tracing, not compiled extensionality through a packaged coordinate four-jet. Necessity/nonemptiness holds under all displayed entrance, regularity, and activity hypotheses. The physical-patch structure packages Ricci decomposition, stress/Hodge data, and the two rescaled Maxwell exterior equations; it does not itself include the scalar wave equation. |
| C9 | Every accepted detector survivor returns physical \(a^2\), and the output image is \(\{a^2\}\), when the accepted set is nonempty and every survivor has the stated physical-branch, probe, regularity, and unique scalar-closure certificate. | **Lean**: `actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted`, `acceptedActualMetricFourthOrderCouplingSqValuesAt_eq_singleton_physical` | Never shorten to an unconditional all-survivor claim.  Unique closure requires \(\neg(O_-=0\wedge O_+=0)\). |
| C10 | The detector is local under equality of coordinate metric germs. | **Lean**: `acceptedActualMetricFourthOrderDetectorChoicesAt_eq_of_eventuallyEq`, `actualMetricFourthOrderCouplingSqCandidateAt_eq_of_eventuallyEq` | Fixed-coordinate locality, not full nonlinear chart covariance. |
| C11 | For the convention-fixed warp constants \(c_1=-1/\sqrt3\), \(c_2=2/\sqrt3\), \(c_3=1\), Kaluza reduction verifies the EMD normalization \(a^2=3\), so detector output \(3\) is necessary on an accepted Kaluza branch. | **Lean** for the full Ricci-block reduction, normalization/selector, and detector specialization | Not sufficient for a metric-only Kaluza uplift. Lean verifies the fixed constants and their matching identities; it does not prove a uniqueness theorem solving a general warp ansatz from Ricci flatness. |
| C12 | An accepted EMD realizer with the additional scalar, Maxwell-potential, and normal-gauge field packages gives the stated local Ricci-flat five-dimensional uplift and orbit. | **Lean**, conditional uplift modules | Conditional handoff at a fixed base-point germ. Its `realize_emd` field already supplies the complete EMD equations, and no concrete inhabitant of that full realizer interface is presently compiled; no global quotient or unconditional curvature-only converse is claimed. |

## Validation claims

| ID | Claim | Evidence | Boundary |
|---|---|---|---|
| V1 | Boosted black-string reduction is a nontrivial \(a^2=3\) convention oracle and returns \(3\) in an active physical channel. | **Exact symbolic**: `vt1b-boosted-black-string` | Repeated Ricci root; outside the simple-spectrum detector branch. |
| V2 | The exact \(a^2=1\) dilaton black hole returns \(1\), is rejected by the Kaluza selector, and its convention uplift is not Ricci flat. | **Exact symbolic**: `vt1c-non-kaluza-dilaton` | Repeated-root physical channel; not complete detector routing. |
| V3 | The helical black-string quotient supplies a nonnull, simple-spectrum, active Kaluza oracle satisfying exact EMD residuals, and its replacement point completes the selected fourth-order route with output \(3\). | **Exact symbolic**: `vt2-generic-helical-string`; `vt2-complete-detector-route` (21 checks) | A 128-slot exact quadratic quotient representation verifies scalar/residual/frame one-jets, all 128 raw channel components, \(A\), physical \(dA=d(\sqrt3 C)\), \(B\), the next-order residual, and output \(3\). The artifact binds the symbolic model, relevant implementation sources, quotient relations, and coefficient payload separately. It does not claim that the 128 slots form a linearly independent number-field basis. Literal quotient \(dA\) is identified by composing compiled physical-germ bridge theorems with exact helical Kaluza EMD patch/open gates; this benchmark-specific composition is neither a brute-force second-jet CAS expansion nor a Lean instance theorem. |
| V4 | A controlled generic perturbation preserves signature/simple spectrum but violates the Kaluza obstruction and Einstein residual. | **Exact symbolic**: `vt2b-generic-near-miss` | A near-miss control, not a completeness theorem. |

## Open claims and prohibited upgrades

| ID | Open question | Do not claim |
|---|---|---|
| O1 | Independent specialist audit of the EMD involutivity extension. | That C5 is machine checked or quoted verbatim from Kruglikov. |
| O2 | Explicit factorization of the complete detector through a coordinate metric four-jet. Current Lean locality assumes equality of metric germs on a neighborhood. | “Four-jet extensionality” or abstract jet naturality as a compiled theorem. |
| O3 | Full nonlinear-coordinate covariance of the complete detector. | “Invariant detector” without the fixed-coordinate qualification. |
| O4 | Converse from metric conditions to an EMD branch and Kaluza uplift. | That output \(3\) is sufficient for uplift. |
| O5 | Density of the active locus. | “Generic” in the dense/open-dense sense; only openness is proved. |
| O6 | Null, zero-scalar, repeated-root, and collision strata. | A classification beyond the stated active simple-spectrum branch. |
| O7 | Global reconstruction and topology. | A global circle bundle, global uniqueness, or global spacetime. |
| O8 | New closed-form exact solution. | That analytic solution germs are new closed-form Kaluza solutions. |
| O9 | A concrete Lean inhabitant of the full physical-patch/survivor and conditional Kaluza-realizer interfaces, and independent literal differentiation of the benchmark quotient field. | That the abstract nonemptiness/uplift packages or the benchmark's last derivative bridge are concrete Lean instance theorems. |

## Citation rule

Every headline claim in the manuscript should cite one or more IDs above.
The formal-PDE realization must always retain its “human + external” label,
and symbolic validation must remain separate from the Lean theorem surface.
