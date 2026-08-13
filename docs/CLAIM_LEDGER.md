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
| C1 | The complete first curvature-seed channel pair has a one-parameter shear kernel and is noninjective in the hidden sine component \(B\). | **Lean**: `canonicalFullComplexionCouplingChannels_shear_invariant`, `canonicalFullComplexionCouplingChannels_not_injective` | A complete-channel obstruction; not yet a solution-level metric-jet theorem by itself. |
| C2 | One fixed active formal metric three-jet supports the displayed truncated EMD data for every real \(a\), with Maxwell first jet injective in \(a\). | **Lean**: `activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling`, `activeAmbiguityMaxwellFirstJet_injective` | Finite-jet statement. |
| C3 | The common Ricci source has four distinct real eigenvalues and the activity wedge is nonzero. | **Lean**: `activeAmbiguityRicciSource_has_four_distinct_real_eigenpairs`, `activeAmbiguityPhysicalComplexion_wedge_component` | Simple-spectrum and active at the marked point; no density claim.  First Bianchi compatibility follows in the human realization argument from the fully symmetric metric three-jet and its proved Ricci first prolongation. |
| C4 | The common metric data are realized by an actual polynomial metric germ through order three, and the closed physical Maxwell one-jet has an explicit radial-gauge potential two-jet. | **Lean**: `activeAmbiguityPolynomialMetricGerm_realizes_threeJet`, `radialGaugePotentialTwoJet4_realizes` | Finite genuine field jets, not an all-order EMD solution by these theorems alone. |
| C5 | Conditional on the explicit analytic EMD involutivity lemma, for every real \(a\) the finite collision extends to a local real-analytic EMD solution germ in pure second-order potential variables \((g,A,\phi)\). | **Human + external**: extension of Kruglikov Theorem 3 by the determined scalar-wave block of Lemma 4, EMD Noether/Bianchi identity, and Cartan--Kähler; proof in `ANALYTIC_EMD_REALIZATION.md` | The finite-jet and gauge completion is closed.  Kruglikov does not state the EMD involutivity lemma verbatim; it remains the single specialist-audit dependency and is not formalized in Lean. |
| C6 | Under C5's explicit involutivity lemma, no function of the metric three-jet identifies \(a^2\) on the analytic family; in particular \(a=\sqrt3\) and \(a=1\) collide. | **Human corollary** of C2--C5 | Equality is in one fixed normal-coordinate chart, which suffices for impossibility.  No common metric four-jet or closed-form spacetime is claimed. |
| C7 | On \(\eta\wedge Jv\ne0\), the next-order constancy equation uniquely recovers \(B\), component independently, and returns \(a^2=A^2+B^2\). | **Lean**: `couplingSqFromNextOrderComponent_eq`, `fourthOrderCouplingSqCandidate_eq_physical` and uniqueness/confluence families | Physical curvature channel.  This does not prove covariance of the complete finite accepted set. |
| C8 | A finite metric-only coordinate detector through order four has an accepted choice returning physical \(a^2\) on the packaged active-regular EMD locus. | **Lean**: `exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD` and physical-active wrappers | Necessity/nonemptiness under all displayed entrance, regularity, and activity hypotheses. |
| C9 | Every accepted detector survivor returns physical \(a^2\), and the output image is \(\{a^2\}\), when every survivor has the stated physical-branch, probe, regularity, and unique scalar-closure certificate. | **Lean**: `actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted`, `acceptedActualMetricFourthOrderCouplingSqValuesAt_eq_singleton_physical` | Never shorten to an unconditional all-survivor claim.  Unique closure requires \(\neg(O_-=0\wedge O_+=0)\). |
| C10 | The detector is local under equality of coordinate metric germs. | **Lean**: `acceptedActualMetricFourthOrderDetectorChoicesAt_eq_of_eventuallyEq`, `actualMetricFourthOrderCouplingSqCandidateAt_eq_of_eventuallyEq` | Fixed-coordinate locality, not full nonlinear chart covariance. |
| C11 | Kaluza reduction selects \(a^2=3\), so detector output \(3\) is necessary on an accepted Kaluza branch. | **Lean** for normalization/selector and detector specialization | Not sufficient for a metric-only Kaluza uplift. |
| C12 | An accepted EMD realizer with the additional scalar, Maxwell-potential, and normal-gauge field packages gives the stated local Ricci-flat five-dimensional uplift and orbit. | **Lean**, conditional uplift modules | Conditional handoff; no global quotient or unconditional curvature-only converse. |

## Validation claims

| ID | Claim | Evidence | Boundary |
|---|---|---|---|
| V1 | Boosted black-string reduction is a nontrivial \(a^2=3\) convention oracle and returns \(3\) in an active physical channel. | **Exact symbolic**: `vt1b-boosted-black-string` | Repeated Ricci root; outside the simple-spectrum detector branch. |
| V2 | The exact \(a^2=1\) dilaton black hole returns \(1\), is rejected by the Kaluza selector, and its convention uplift is not Ricci flat. | **Exact symbolic**: `vt1c-non-kaluza-dilaton` | Repeated-root physical channel; not complete detector routing. |
| V3 | The helical black-string quotient supplies a nonnull, simple-spectrum, active Kaluza oracle satisfying exact EMD residuals. | **Exact symbolic**: `vt2-generic-helical-string` | At the replacement point, the pointwise upstream route and physical active wedge pass; the final selected fourth-order derivative and complete accepted choice are not yet evaluated. |
| V4 | A controlled generic perturbation preserves signature/simple spectrum but violates the Kaluza obstruction and Einstein residual. | **Exact symbolic**: `vt2b-generic-near-miss` | A near-miss control, not a completeness theorem. |

## Open claims and prohibited upgrades

| ID | Open question | Do not claim |
|---|---|---|
| O1 | Independent specialist audit of the EMD involutivity extension. | That C5 is machine checked or quoted verbatim from Kruglikov. |
| O2 | Complete accepted-choice routing of the positive generic benchmark. | That the new analytic collision germs or current benchmark pass every finite detector gate. |
| O3 | Full nonlinear-coordinate covariance of the complete detector. | “Invariant detector” without the fixed-coordinate qualification. |
| O4 | Converse from metric conditions to an EMD branch and Kaluza uplift. | That output \(3\) is sufficient for uplift. |
| O5 | Density of the active locus. | “Generic” in the dense/open-dense sense; only openness is proved. |
| O6 | Null, zero-scalar, repeated-root, and collision strata. | A classification beyond the stated active simple-spectrum branch. |
| O7 | Global reconstruction and topology. | A global circle bundle, global uniqueness, or global spacetime. |
| O8 | New closed-form exact solution. | That analytic solution germs are new closed-form Kaluza solutions. |

## Citation rule

Every headline claim in the manuscript should cite one or more IDs above.
The formal-PDE realization must always retain its “human + external” label,
and symbolic validation must remain separate from the Lean theorem surface.
