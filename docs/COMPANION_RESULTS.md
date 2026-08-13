# Companion results and latent paper directions

Date: 2026-08-13

Status: ranked map of compiled supporting results; not part of the active
paper's headline claim surface

The coupling-identifiability theorem remains the north star.  This note keeps
several substantial results discoverable without expanding the manuscript or
research plan.  The ranking is by plausible standalone mathematical value,
not by priority or verified novelty.

## 1. Exact scalar-branch orbit and differential classifier

On the complementary simple-spectrum scalar block, the unresolved relative
sign is not an arbitrary algebraic accident: the two solutions are exchanged
by a Ricci-centralizing spectral reflection.  At first differential order,
the curvature data fall exhaustively into exactly four closure outcomes:
plus only, minus only, both, or neither.  Separate finite witnesses can reject
both branches on a patch.

Lean anchors:

- `scalarComplementarySolutions_eq_or_flip`;
- `secondSpectralReflection_commutes_with_Ricci`,
  `secondSpectralReflection_preserves_Ricci`, and
  `secondSpectralReflection_conjugates`;
- `exhaustive_closure_classification`, `closureOutcome_eq_plusOnly_iff`,
  `closureOutcome_eq_minusOnly_iff`, `closureOutcome_eq_both_iff`, and
  `closureOutcome_eq_neither_iff`;
- `neither_curvatureBranch_closesOn_of_witnesses` and
  `exhaustive_patch_closure_classification`.

Boundary: this is the stated complementary simple-spectrum branch.  When both
branches close it does not identify which scalar branch is physical, and it
does not classify null, repeated-root, or collision strata.

## 2. Maxwell duality as an orbit, cocycle, and EMD symmetry breaking

For a nonzero canonical Maxwell amplitude pair, equality of stress magnitude
is equivalent to membership in one unit-duality orbit, and the acting
parameter is unique.  Transition parameters compose with an exact overlap
cocycle; their infinitesimal complexion rates obey the corresponding
connection law, and subtracting a local connection removes the inhomogeneous
term.  In active nonzero-coupling EMD, constant duality is reduced from the
full circle to overall sign.  The full constant-duality circle returns on the
zero-coupling or inactive scalar-source loci.

Lean anchors:

- `exists_dualityParameter_iff_same_magnitude`,
  `dualityParameter_unique`, and `duality_overlap_cocycle`;
- `complexionRate_variable_duality_add`,
  `complexionRate_dualityComposeDerivative`, and
  `gaugeCorrectedComplexionRate_invariant`;
- `physicalComplexionOneFormFromDoubleAngle_eq_dualityComplexion` and
  `coordinatePhysicalComplexionOneForm_changeBasis`;
- `constantDuality_emd_iff_sign_of_active`,
  `constantDuality_emd_of_inactive_source`, and
  `constantDuality_emd_of_zero_coupling`.

Boundary: the algebraic orbit theorem is finite dimensional, while the
physical-complexion files provide the relevant patchwise field bridges.  No
global duality bundle or topological classification is claimed.

## 3. Intrinsic local Kaluza reduction and exhaustive presentation freedom

For the actual normal/radial-gauge local product fields, the complete
five-dimensional Ricci calculation is equivalent to the convention-fixed EMD
equations.  This equivalence persists under arbitrary invertible nonlinear
coordinate three-jets, including changes mixing base and circle directions.
Separately, two product-preserving Kaluza block presentations are equivalent
exactly when their warped base, fiber radius, and connection satisfy three
explicit compatibility conditions.  Gauge shifts, fiber reversal, and the
dilaton-shift/circle-radius modulus occur inside that exhaustive orbit.

Lean anchors:

- `nonlinearLocalProductCoordinateRicciFlat_iff_emd`,
  `ricciFlatInChart_iff_ricciFlatInChart`, and
  `intrinsicRicciFlatAt_iff_emd`;
- `equivalentUnder_iff_compatible`, `equivalentUnder_gauge`,
  `exists_localGaugeFiberCoordinate_of_sameCurvature`,
  `equivalentUnder_fiberReversal`, and `equivalentUnder_dilatonShift`.

Boundary: this is a local, convention-fixed theorem from supplied EMD and
normal-gauge field data.  It is not a metric-only converse, global circle
bundle theorem, or classification under every non-product presentation.

## 4. Reusable exact finite-jet realization layer

The collision data are not merely formal arrays.  A cubic polynomial metric
field realizes their symmetric metric three-jet, and every closed Maxwell
one-jet has an explicit radial-gauge potential two-jet.  These constructions
are reusable for finite-jet counterexamples and formal-PDE entrance data.

Lean anchors:

- `activeAmbiguityPolynomialMetricGerm_realizes_threeJet` and
  `coordinateRicciFirstJet_minkowski_zero`;
- `radialGaugePotentialTwoJet4_realizes`.

Boundary: finite genuine field jets are not automatically all-order PDE
solutions.  The active collision's analytic solution-germ promotion retains
the separate human-plus-external involutivity status in
[`ANALYTIC_EMD_REALIZATION.md`](ANALYTIC_EMD_REALIZATION.md).

## Use after the current paper

The most coherent follow-up is the duality-orbit/connection result, followed
by the intrinsic Kaluza reduction and presentation-orbit theorem.  The branch
classifier is a natural technical companion.  None should displace the
current paper until its formal-PDE audit and submission hardening are complete.
