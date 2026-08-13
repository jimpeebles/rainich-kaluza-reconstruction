# Research roadmap

The governing plan is [`docs/RESEARCH_RESET.md`](docs/RESEARCH_RESET.md).
This file is only its compact execution view.

## North star

Prove a generic local Rainich–Kaluza identifiability theorem:

> A finite covariant construction from a four-dimensional Lorentzian metric
> and its finite jet reconstructs the admissible EMD branches and their
> coupling magnitude. It recognizes the Kaluza sector by `aGeomSq = 3` and,
> after explicit integrability obstructions, constructs the local
> five-dimensional Ricci-flat circle uplift up to its natural orbit.

The first differentiated Rainich channels have a proved shear kernel. One
further coordinate derivative recovers `aGeomSq` on the active locus; full
realization may honestly require derivatives through order five.

The order separation now has an exact active formal witness. The Kaluza value
`a²=3` and a non-Kaluza value `a²=1` share one explicit normal-coordinate
metric three-jet satisfying the point Einstein and scalar equations and the
first Ricci prolongation, while their distinct Maxwell first jets satisfy both
exterior equations and point/first-jet Hodge compatibility. The
product-rule `CoordinateRicciFirstJet` bridge gives the Ricci-prolongation
statement its literal coordinate meaning. This is a finite formal-jet
collision, not a pair of local solutions or an all-order integrability result.
For this witness the order jump is explicit: both couplings share the complete
first channel `(A,eta)=(0,e₂)`, whereas the fixed active next-order component
recovers `B=√3` and `B=1`, producing squared outputs `3` and `1`.

## Current gate — exact routing and publication theorem presentation

Prove that every packaged Ricci--exterior EMD witness satisfying the active
regular hypotheses supplies a survivor of the complete finite actual-metric
detector and that, on the explicit unique
scalar-closure locus, every pointwise survivor returns the same `a²`. The
regularity, physical-complexion, nonemptiness, and confluence ingredients are
now compiled; the immediate tasks are complete-detector benchmark routing and
a clean publication theorem statement with every hypothesis exposed.

Current substeps:

1. **Arbitrary-basis Lorentzian frame signs — implemented and proved.** For a
   rank-two projector range containing a timelike vector in an index-one
   metric, any ambient basis supplies two projected basis vectors and one of
   six explicit recipes giving both strict Gram–Schmidt signs. The complete
   detector enumerates the recipe and builds its coframe from the resulting
   smooth metric-dependent fields.
2. **Coordinate-matrix pointwise specialization — complete.**
   `exists_smoothMatrixProjectedBasisLorentzianFrameSignsAt` translates the
   abstract basis theorem to the repository's matrix projector and smooth
   pivot fields at an arbitrary coordinate point.
3. **Neighborhood persistence — complete.**
   `exists_eventually_smoothMatrixProjectedBasisLorentzianFrameSignsAt`
   proves that one fixed coordinate pair and pivot recipe retain both strict
   signs on a neighborhood whenever the metric and projector entries are
   continuous at the base point.
4. **Physical Maxwell frame entrance — complete for any fixed scalar
   branch.** Positive observer energy now forces the negative Maxwell
   projector to contain a timelike direction; the square law and trace force
   both projector ranges to have rank two. The detector then selects all four
   coordinate probes and a pivot recipe with all four strict signs on one
   neighborhood. No preferred frame is assumed.
5. **Finite scalar probes — complete.** Algebraic idempotence and trace one
   force both complementary projectors to have rank one. Intrinsic timelike
   and spacelike labeling then makes an arbitrary coordinate basis contain an
   admissible projection on each line, with both signs persistent locally.
   Normalized representatives are unique up to sign. The projected-probe
   two-line theorem further proves that the enumerated sum/difference branches
   recover the same metric-dual covector orbit as any physical normalized
   representatives, up to one overall sign. Thus neither probe choice nor the
   relative-sign bit remains an identifiability assumption.
6. **True coframe, coordinate Hodge naturality, and finite orientation —
   complete pointwise.**
   The arbitrary-chart detector now uses the inverse tetrad as its dual
   coframe. Maxwell algebra and frame signs prove `LᵀηL=G`. An explicit
   determinant-`-1` reflection fixes the electric seed and negates the Hodge
   seed. Determinant covariance of the explicit alternating symbol proves the
   coordinate Hodge formula natural up to orientation and exactly natural for
   `det L>0`. A non-circular detector wrapper derives exact Hodge compatibility
   from the coframe metric identity, Maxwell/frame gates, and positive
   determinant; the finite reflection supplies the positive branch.
7. **Physical scalar value and first-jet identifiability — complete on the
   stated regular patch.**
   `PhysicalScalarIdentifiability.lean` proves that the
   reconstruction equation in a generic pseudo-orthonormal Ricci eigenbasis
   forces both complementary component magnitudes, kills both protected-root
   components off the explicit resonances, and makes the finite projected-
   probe list contain the physical covector up to global sign.
   `ActualMetricScalarIdentifiability.lean` now instantiates the actual
   polynomial projectors, rank and causal-line facts, coordinate probes, and
   stored detector candidate. The choice-independent EMD Ricci witness is now
   defined, and its physical Ricci decomposition plus Maxwell square law
   derive reconstruction and a literal finite candidate equal to the physical
   scalar up to sign. The patch witness and fixed-probe theorem now give a
   pointwise two-branch cover; nonzero-component separation and continuity
   select one branch and one global sign locally, and actual Frechet-derivative
   transfer proves that branch's literal fourth-order closure obstruction is
   zero. The selected branch now also clears the detector's literal
   reconstruction and packaged Maxwell gates: the global sign cancels in the
   rank-one tensor, the physical Ricci decomposition yields the exact matrix
   identity, and the physical Maxwell square/self-adjointness laws yield the
   residual and principal-projector tests. The positive-energy frame and exact
   Hodge-orientation selectors are now composed as well: one raw choice passes
   every upstream metric gate. The fixed-choice neighborhood-promotion theorem
   now retains that same raw choice, its scalar `±` germ, and all four frame
   signs on an honest smaller open patch. Its only new local regularity inputs
   are continuity of the two strict reconstructed diagonal amplitudes and of
   the selected coframe entries. Upstream entrance itself implies `det L>0`,
   so exact positive-orientation Hodge compatibility persists automatically.
8. **Finite channel selection and conditional physical splice — complete.** The
   former universal genericity premise was vacuous because diagonal wedge
   choices are enumerated and rejected. It has been replaced by the intrinsic
   active-wedge condition, proved equivalent to existence of a finite generic
   source/wedge choice. The active wedge is exactly
   `dtheta ∧ J(dphi) != 0`, independent of the hidden sine channel. Direct
   acceptance from upstream + physical channel + selected component is now
   proved. The full Maxwell stress-fibre theorem is also proved pointwise in
   arbitrary adapted coordinates. Its smooth patch version supplies
   constructive unit-duality coordinates and the complexion one-form when the
   positive amplitude, physical form, adapted coframe, and coframe/stress
   identities hold smoothly throughout that patch. A new quotient-germ theorem proves that local physical
   channel equality automatically identifies the detector's Frechet-derived
   quotient with the physical double-angle derivative. The selected upstream
   coframe now also has proved inverse-metric identities and a patchwise smooth
   stress-fibre theorem. A separate `C¹` germ-transfer theorem shows that
   equality of the physical and reconstructed Maxwell/Hodge fields on a
   neighborhood forces equality of their first jets and transports the EMD
   exterior closure. `NorthStarComposition.lean` now derives those two field
   germs instead of assuming them: reconstructed stress puts the physical
   field on the smooth duality orbit, and the positive determinant already
   implied by upstream plus the physical Hodge relation fixes its partner with
   the same complexion. Thus a genuine `C¹` pair on a smooth upstream patch,
   with reconstructed
   stress, physical Hodge relation, EMD closure, scalar continuity, and an
   active wedge, produces a finite accepted choice with output `a²`; adding
   `a²=3` gives the Kaluza output `3`. Scalar orientation may replace `a` by
   `-a` but preserves the output.
9. **Invariant-EMD composition, conventional regularity, and physical
   activity — implemented.**
   `InvariantEMDDetectorComposition.lean` packages a detector-choice-free
   genuine EMD `C¹` Maxwell/Hodge pair, physical stress, metric-Hodge
   relation, and exterior closure. It intersects the scalar `±` germ with the
   upstream germ on one open selected patch and correlates that sign with
   coupling `a` or `-a`. `InvariantEMDEndToEnd.lean` composes the finite
   upstream selector and proves that the metric-only accepted set contains a
   survivor with `aGeomSq=a²` (`3` under Kaluza normalization).
   `ActualMetricDetectorRegularity.lean` derives the selected coframe and
   protected positive magnitude at `C²` from conventional `C²` regularity of
   `g`, the selected residual, and `qSq`; the regularity end-to-end module
   substitutes these derived facts for bespoke premises. The selector-
   certificate integration is included in the passing 2,912-job repository
   build and axiom audit.

   `PhysicalComplexionInvariant.lean` defines the physical one-form
   `omega=(C dS-S dC)/2` directly from physical `F`, its Hodge partner, inverse
   metric, and `q`; proves frame and simultaneous physical-pair-sign
   invariance; derives the source-free physical effective channel; and proves
   that the detector active gate is equivalent to the choice-free physical
   Maxwell-complexion/stress wedge, including the scalar-orbit variant.
   `InvariantActiveWedgeOpenness.lean` proves this locus is open under
   continuity and persists locally from `ContinuousAt`; density is not
   asserted.
10. **Pointwise all-survivor identifiability — complete on the sharp locus.**
   `InvariantEMDConfluence.lean` defines
   `IsActualMetricUniqueScalarClosureBranchAt4`, namely
   `¬(O_false=0 ∧ O_true=0)`, and proves that every pointwise member of the
   finite accepted set returns the physical `a²` under conventional local
   regularity and admissible-probe hypotheses. Hence any two survivors agree
   there. No unconditional claim is made on the two-closed-branch locus: both
   relative-sign branches may close, so the present data do not identify one
   physical branch. `InvariantEMDPublicationCorollaries.lean` now packages
   these per-survivor hypotheses and proves that the complete finite output
   image is `{a²}` from accepted-set nonemptiness plus a certificate for each
   accepted choice.
11. **Final invariant nonemptiness composition — complete.**
   `exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd_physicalActive`
   takes the conventional selector and regularity data, one choice-free
   physical Maxwell-complexion activity premise, and a callback supplying only
   selected-residual `C²`. It concludes that the metric-only accepted set has
   a member returning physical `a²`; the Kaluza corollary returns `3`.
12. **Active formal lower-order collision and fixed-coordinate locality —
    complete.** `ThirdOrderMatterJetAmbiguity.lean` exhibits the common active
    formal metric three-jet at `a=√3` and `a=1`, with all point/first-jet
    equations stated above. `CoordinateRicciFirstJet.lean` identifies its
    normal-frame Ricci derivative with the product-rule derivative of the
    coordinate Ricci formula. `ActualMetricDetectorLocality.lean` proves that
    neighborhood-equal coordinate metric fields give the same complete finite
    accepted set and the same numerical raw-choice outputs. The latter is
    fixed-coordinate germ extensionality, not chart covariance.
13. **Exact check and theorem presentation — active.** The routing audit found
   that the original helical point is outside the detector's causal scalar
   branch and therefore has an empty accepted set. A replacement interior
   point now passes the entire exact pointwise upstream predicate, including
   reconstruction, Maxwell projectors, a finite signed frame, oriented Hodge
   compatibility, and the choice-free physical active wedge. The remaining
   route is the selected fourth-order frame/channel derivative and accepted
   output. Complete that route, and state the
   necessity plus unique-closure pointwise-confluence theorem compactly for
   publication without hiding its regularity or admissible-probe assumptions.

Exit theorem: the detector takes only `g` and explicit generic hypotheses;
genuine constant-coupling EMD implies its accepted set is nonempty, and on
the explicit unique scalar-closure locus every accepted result equals the
physical `a²` (`3` for Kaluza).

## Next gate — finite-jet converse

After the entrance theorem closes:

1. impose and analyze the reconstructed `dB` and `d(aGeomSq)` obstructions;
2. accept metric order five if differentiating `B` is genuinely necessary;
3. reconstruct the complexion, physical Maxwell field, and constant coupling;
4. compose with the proved local uplift and orbit theorem;
5. state the necessary-and-sufficient generic recognition theorem.

## Explicitly deferred

Do not divert the main effort to null/repeated-root branches, global topology,
new exact-solution generation, extra uplift plumbing, phenomenology, or
manifold-library migration until the two gates above close.

## Publication boundary

- The compiled active-regular finite-coordinate necessity/identifiability
  theorem is a strong detector-paper nucleus even without the converse;
  nonlinear-coordinate covariance is a separate upgrade.
- The active `a²=3` versus `a²=1` formal metric-three-jet collision is a
  sharp lower-order companion theorem only at the finite formal-jet level; it
  is not advertised as a collision between actual local EMD solutions.
- The full necessary-and-sufficient uplift theorem is the landmark result.
- The helical black-string reduction is validation, not a new local solution.
- Any priority claim remains provisional pending specialist review.
