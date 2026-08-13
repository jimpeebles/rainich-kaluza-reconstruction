# North-star research plan: generic Rainich–Kaluza identifiability

Date adopted: 2026-08-12  
Last recalibrated: 2026-08-12 after conventional regularity discharge,
choice-free physical-complexion activity, and unique-closure confluence

This is the repository's **single operational research plan**. `ROADMAP.md` is
its compact execution view. `CLAIM_LEDGER.md` is the exact truth ledger.
Historical phase plans are redirects only and must not create work.

## The north star

Prove the following generic local theorem.

> **Generic Rainich–Kaluza recognition.** On an explicitly stated oriented
> Lorentzian patch, a finite covariant algorithm taking only the metric and its
> finite jet returns the admissible Einstein–Maxwell–dilaton reconstructions,
> determines their coupling magnitude, and recognizes five-dimensional vacuum
> Kaluza origin by `aGeomSq = 3` together with explicit integrability
> obstructions. Every accepted branch yields a local Ricci-flat circle uplift,
> unique up to the expected scalar, duality, gauge, and fibre-coordinate orbit.

The target has two honest layers:

1. a fourth-order **necessity/identifiability theorem**;
2. a finite-order **necessary-and-sufficient realization theorem**, allowed to
   use the metric five-jet if the reconstructed `dB` equation requires it.

The first layer is the immediate publication target. The second is the
landmark result.

## Frozen immediate theorem — do not move the goalposts

The current turn-level target is the following one theorem, not another phase
or intermediate architecture:

> Let `g` be a sufficiently differentiable Lorentzian metric on a connected
> local patch. Assume the explicit active regular gates: four real simple
> Ricci roots in the labeled nonresonant branch, positive non-null Maxwell
> square, causal complementary scalar eigenlines, positive Maxwell energy,
> and the choice-free physical active wedge. If `g` carries the packaged
> constant-coupling Ricci--exterior EMD witness, then the finite set
> `acceptedActualMetricFourthOrderDetectorChoicesAt g z` is nonempty. Every
> pointwise survivor carrying its explicit realized-branch, probe, regularity,
> and unique scalar-closure certificate returns the same physical `a²`; at
> Kaluza coupling it returns `3`.

The physical EMD fields occur only in the necessity/correctness proof. The
accepted set itself continues to take only `g`. A result counts as progress
only when it closes one premise of this statement.

| Premise | Status |
|---|---|
| finite scalar probes and relative sign recover the physical scalar value | closed |
| selected literal scalar branch clears the reconstruction gate | closed |
| finite Maxwell principal frame exists from positive energy | closed |
| true arbitrary-chart dual coframe reconstructs `g` | closed |
| explicit coordinate Hodge star is natural up to determinant sign and exactly natural for a positive-determinant coframe | closed |
| a finite positive-orientation bit passes exact Hodge equality without an independent Hodge-sign premise | closed pointwise |
| one fixed scalar branch agrees with the physical closed scalar field to first order on a neighborhood | closed |
| scalar/Maxwell/Hodge selectors compose to one complete upstream choice | closed |
| continuity of the two strict reconstructed diagonal amplitudes and selected coframe entries promotes that same choice, scalar `±` germ, and frame signs to an honest open patch with upstream entrance everywhere | closed |
| upstream entrance implies `det L>0`, hence exact positive-orientation Hodge convention on the whole selected patch | closed |
| intrinsic active wedge selects one finite source/wedge component | closed |
| arbitrary-frame non-null Maxwell stress fibre is the unit duality orbit pointwise, with explicit smooth coordinates on every positive adapted patch satisfying the coframe and stress identities | closed |
| the selected actual-metric upstream coframe canonically diagonalizes its Maxwell residual and puts every physical stress witness in that duality orbit | closed pointwise |
| any local physical channel germ forces the detector's actual quotient derivative to be the double-angle derivative | closed |
| equality of genuine physical and reconstructed `C¹` Maxwell/Hodge field germs identifies their stored first jets and transfers EMD exterior closure | closed |
| reconstructed stress, `det L>0`, and the physical Hodge relation derive the physical/reconstructed Maxwell/Hodge field germs on the patch | closed |
| a genuine `C¹` Maxwell/Hodge pair on a smooth upstream patch, with reconstructed stress, physical Hodge relation, EMD closure, scalar continuity, and an active wedge, produces a finite accepted choice with output `a²` (`3` at Kaluza coupling) | closed conditionally on those physical and regularity data; positivity follows from upstream |
| package conventional invariant EMD physical fields, stress, Hodge relation, and closure without a detector choice, and align scalar/coupling `±` | closed |
| intersect the selected scalar-sign germ and upstream germ into one honest open patch and compose the finite selector to an accepted output `a²` (`3` at Kaluza coupling) | closed |
| derive selected `C²` coframe/magnitude regularity from conventional `C²` regularity of `g`, the residual, and `qSq` on an upstream patch | closed in `ActualMetricDetectorRegularity.lean` and the regularity end-to-end composition; included in the passing 2912-job root build |
| construct the choice-free physical complexion covector from `F`, its Hodge partner, inverse metric, and `q`; derive the source-free physical effective channel; identify its stress wedge exactly with detector activity and prove the active set is open under continuity | closed in `PhysicalComplexionInvariant.lean` and `InvariantActiveWedgeOpenness.lean`; openness is proved, density is not claimed |
| every pointwise accepted survivor returns physical `a²` | closed on `¬(O_false=0 ∧ O_true=0)`, with the displayed conventional local regularity and admissible-probe hypotheses; unsupported without that sharp exclusion |
| compose conventional selector/regularity data and one choice-free physical activity premise into final invariant nonemptiness with output `a²` (`3` for Kaluza) | closed in `InvariantEMDPhysicalActiveEndToEnd.lean`; the residual callback is restricted to selected choices and supplies only residual `C²` |

## Why this is the right result

Kaluza reduction maps five-dimensional vacuum geometry to a distinguished
four-dimensional scalar–Maxwell theory. Rainich reconstruction asks whether
matter can instead be recovered from four-dimensional curvature. This project
joins those forward and inverse problems for the coupled Kaluza EMD sector.

A new boosted or twisted reduction of a known seed does not by itself advance
that problem. The current helical Schwarzschild-string reduction is an exact
validation oracle, not a new local five-dimensional geometry.

## Proved scientific nucleus

On the stated non-null, real simple-spectrum branch:

1. the actual metric constructs the Ricci spectral data, zero/one/two scalar
   branches, Maxwell residual, principal projectors, Hodge partner, and a
   finite obstruction-filtered detector;
2. the complete first differentiated curvature-seed channels determine
   `A = a cos(2θ)` and `eta = dθ + (B/2)Jv`, but have the exact shear kernel
   `B ↦ B+τ`, `dθ ↦ dθ-(τ/2)Jv`;
3. constancy of the physical coupling gives
   `dA + 2B eta - B²Jv = 0`, which generically reconstructs `B` and
   `aGeomSq = A²+B² = a²` one metric derivative later;
4. genuine EMD exterior closure implies the canonical physical channel; on
   the positive-`q`, nonzero-source, nondegenerate-wedge locus the transported
   detector is nonempty and every accepted result is `a²`;
5. the fixed scalar/frame/orientation choice promotes to an honest smaller
   open upstream patch under continuity of the two reconstructed diagonal
   amplitudes and selected coframe entries; upstream itself implies positive
   coframe determinant throughout that patch;
6. on a smooth actual-metric upstream patch, genuine `C¹`
   physical Maxwell/Hodge fields with reconstructed stress, the metric-Hodge
   relation, EMD closure, scalar continuity, and an active wedge produce a
   finite accepted choice with output `a²`; at Kaluza coupling the specialized
   theorem returns `3`;
7. the physical/reconstructed field germs used in that proof are derived from
   stress, positive orientation, and the physical Hodge relation rather than
   assumed;
8. a detector-choice-free physical EMD patch is now composed with the selected
   scalar/upstream germs, automatically replacing `a` by `-a` on the negative
   scalar branch; the end-to-end theorem returns a metric-only accepted
   survivor with output `a²`, or `3` at Kaluza coupling, under the explicit
   selected regular-locus hypotheses;
9. the selected coframe and positive Maxwell magnitude have `C²` regularity
   as consequences of ordinary `C²` regularity of the metric, selected
   residual, and reconstructed `qSq` on the upstream patch; they are no longer
   bespoke regularity assumptions;
10. the physical double-angle fields construct the choice-free one-form
   `omega=(C dS-S dC)/2`; it is frame and simultaneous field-sign invariant,
   agrees with `c ds-s dc`, supplies the physical effective channel without a
   source choice, and makes the detector active gate exactly the invariant
   physical Maxwell-complexion/stress wedge. Under continuity this active set
   is open and activity persists on a neighborhood; density is not claimed;
11. on the sharp unique scalar-closure locus
   `¬(O_false=0 ∧ O_true=0)`, every pointwise accepted finite choice returns
   the physical `a²` under conventional local regularity and admissible-probe
   hypotheses. This is the all-survivor identifiability statement; no such
   unconditional conclusion is asserted where both scalar branches close.
   The publication corollary packages one certificate per survivor and proves
   the complete finite output image is exactly `{a²}` once nonemptiness holds;
12. the final physical-active end-to-end wrapper composes the explicit
    selector/regularity hypotheses and one choice-free physical activity
    premise into metric-only accepted-set nonemptiness with output `a²`, or
    `3` under Kaluza normalization;
13. the local EMD-to-Ricci-flat uplift, converse reduction, and presentation
   orbit are already proved conditional on an accepted EMD realization.

The Lean build is placeholder-free, and the exact suite contains a nonzero
Kaluza convention ladder, an `a²=1` EMD rejection, a generic Kaluza positive,
and a paired non-EMD near miss.

## Current gate: exact routing and publication statement

The one active objective is:

> `InvariantEMDDetectorComposition.lean` now packages the conventional
> detector-choice-free physical EMD fields, stress, metric-Hodge relation, and
> exterior closure. It intersects the selected scalar `±` germ with the
> upstream germ on one honest open patch and aligns coupling `a` or `-a`.
> `InvariantEMDEndToEnd.lean` composes the finite upstream selector with this
> theorem and returns an accepted metric-only branch with `aGeomSq=a²`; its
> Kaluza specialization returns `3`.
>
> `ActualMetricDetectorRegularity.lean` now derives the selected principal
> coframe and positive magnitude at `C²` from conventional `C²` regularity of
> `g`, the selected Maxwell residual, and reconstructed `qSq` on the upstream
> patch. `InvariantEMDRegularityEndToEnd.lean` substitutes those derived facts
> for the former bespoke coframe/magnitude premises. The selector-certificate
> integration and final physical-active wrapper are included in the passing
> full repository build.
>
> `PhysicalComplexionInvariant.lean` constructs the choice-free physical
> double-angle fields and `coordinatePhysicalComplexionOneForm =
> (C dS-S dC)/2` from physical `F`, its Hodge partner, inverse metric, and `q`.
> It proves frame and simultaneous physical-pair-sign invariance, equality
> with `c ds-s dc`, the source-free physical effective-channel theorem, and
> exact equivalence between detector activity and the invariant physical
> Maxwell-complexion/stress wedge (also across the scalar `±` orbit).
>
> `InvariantEMDConfluence.lean` proves pointwise accepted-set correctness on
> `IsActualMetricUniqueScalarClosureBranchAt4`, exactly
> `¬(O_false=0 ∧ O_true=0)`: under ordinary local regularity and admissible
> probe hypotheses, every accepted finite choice returns physical `a²`.
> Thus survivor confluence is closed on this sharp locus. If both literal
> scalar branches close, the current geometry can support two candidates and
> unconditional identifiability is not proved or claimed.
>
> `InvariantEMDPhysicalActiveEndToEnd.lean` now performs the final necessity
> composition. The theorem
> `exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd_physicalActive`
> takes the conventional selector and regularity data, exactly one
> choice-free physical Maxwell-complexion activity premise, and a callback
> supplying only selected-residual `C²`; it concludes that the finite
> metric-only accepted set contains an output `a²`. Its Kaluza corollary
> returns `3`. These regularity and probe hypotheses remain explicit; the
> theorem does not replace them by an unqualified appeal to smoothness.
>
> The active tasks are now to route a positive active benchmark through the
> complete detector and present the necessity plus unique-closure confluence
> result cleanly in the manuscript. The full converse remains a separate later
> theorem.

An adversarial audit exposed and repaired an important quantifier error in
the former conditional theorem: genericity cannot hold for *every* upstream
raw choice, because the finite enumeration intentionally includes diagonal
wedge indices and rejects them. The correct statement is existential.
`IsActualMetricActiveFourthOrderWedgeAt` is now proved equivalent to existence
of an enumerated generic component, and direct acceptance is proved from an
upstream choice plus a physical channel. Moreover
`eta = omega + (B/2)Jv` implies `eta ∧ Jv = omega ∧ Jv`, so the genuine generic
locus is the coupling-independent geometric condition
`dtheta ∧ J(dphi) ≠ 0`.

The former chart defect was that the Lorentzian Maxwell principal plane may
have no timelike projection among the four individual coordinate-basis
vectors. The detector no longer makes that assumption:

- `LorentzianPivotRecipe` enumerates six algebraic combinations of a projected
  coordinate pair;
- `exists_lorentzianPivotRecipe_of_gramDet_neg` proves that a pair with
  negative Gram determinant supplies a timelike pivot and a valid
  Gram–Schmidt companion;
- `exists_projectedBasisPair_gramDet_neg` proves that every ambient basis
  supplies such a projected pair when the projector range is rank two and
  contains a timelike vector in an index-one metric;
- `exists_projectedBasisLorentzianFrameSigns` composes both facts into the two
  strict signs required by Lorentzian Gram–Schmidt;
- smooth field-level pivot and companion constructors are proved;
- `exists_eventually_smoothMatrixProjectedBasisLorentzianFrameSignsAt`
  selects one fixed coordinate pair and recipe whose two signs persist on a
  neighborhood under pointwise continuity;
- positive observer energy for a self-adjoint non-null Maxwell residual now
  proves that its negative projector range contains a timelike direction;
  the square law and trace force both principal ranges to have rank two;
- `exists_eventually_actualMetricMaxwellFrameChoice_of_positiveEnergy`
  consequently selects all four Maxwell coordinate probes and the pivot
  recipe, with all four strict frame signs valid on one neighborhood for any
  fixed scalar branch passing the metric Maxwell gate;
- `ActualMetricDetectorChoice4` now enumerates the pivot recipe and constructs
  the principal coframe from those metric-dependent fields.
- the analogous scalar-probe defect is also closed:
  idempotence plus trace one is proved to make each complementary projector
  rank one; an arbitrary ambient basis must contain a nonzero projection onto
  any rank-one range; intrinsic timelike/spacelike labeling therefore selects
  one of the four coordinate probes on each scalar eigenline, with both signs
  persistent on a neighborhood;
- `rankOneRange_normalizedVectors_eq_or_neg` proves that any two normalized
  representatives of the same scalar eigenline differ only by global sign.
  More strongly,
  `exists_relativeSignMetricDualCombination_eq_or_neg_of_projectedProbes`
  proves that arbitrary admissible projected probes on the two rank-one
  eigenlines produce the same two-component metric-dual covector orbit as
  the physical normalized eigenline representatives, up to the enumerated
  relative-sign bit and one common global sign. Hence probe choice and
  relative-sign enumeration create no additional ambiguity. The formerly
  missing implication from the EMD Ricci equation to the two reconstructed
  scalar-gradient components is also closed:
- that physical implication is now proved at the abstract spectral-frame
  level in `PhysicalScalarIdentifiability.lean`:
  `reconstructionEquation_scalarCovector_eigencomponent` forces each scalar
  component magnitude, protected nonresonant roots carry zero scalar
  component, and a pseudo-orthonormal Ricci eigenbasis leaves support only on
  the two complementary lines. The composed theorem
  `exists_projectedProbeScalarBranch_eq_or_neg_of_reconstructionEquation`
  then proves that the detector's finite projected-probe list contains the
  physical scalar covector up to global sign.
- the actual-metric projector/probe instantiation is now proved in
  `ActualMetricScalarIdentifiability.lean`:
  `exists_actualMetricFiniteProbeScalarBranch_eq_or_neg_of_physicalCovector`
  derives the rank-one projectors, finite coordinate probes, amplitudes, and
  relative-sign choice from the actual metric gate and concludes that one
  literal stored scalar candidate equals the physical covector up to global
  sign. `ChoiceIndependentActualMetricEMDRicciWitnessAt4` now freezes the
  correctness-side physical entrance without any detector choice, and
  `exists_actualMetricFiniteProbeScalarBranch_eq_or_neg_of_emdRicciWitness`
  derives the reconstruction equation from the physical rank-one Ricci
  decomposition and Maxwell square law before invoking the finite selector.
  The local seam is now closed. A patchwise choice-independent EMD Ricci
  witness makes any fixed admissible probe pair's two literal candidates
  cover the physical `±` orbit pointwise. Continuity and nonzero spectral
  components exclude branch switching, while a nonzero physical scalar
  excludes sign switching. The surviving field therefore equals one fixed
  sign of the closed physical scalar on a smaller neighborhood, and
  `exists_actualMetricScalarClosureObstruction_eq_zero_of_emdRicciWitnessPatch`
  proves that one literal fourth-order scalar closure obstruction vanishes;
- the arbitrary-chart coframe representation has been corrected and proved:
  the detector now uses the inverse tetrad matrix `E⁻¹`, not the row display
  `Eᵀ`, as the true dual coframe. Maxwell algebra plus the four strict signs
  prove the tetrad pseudo-orthonormal and then prove exactly
  `Lᵀ minkowskiMetric L = G` for the actual coordinate metric;
- a new finite orientation bit acts by reflection of the last canonical
  spacelike leg. The reflection preserves `minkowskiMetric`, has determinant
  `-1`, fixes the canonical electric seed, and negates its canonical Hodge
  partner. Thus orientation reversal does exactly what the detector needs and
  changes no frame sign or residual;
- The standard coordinate Hodge naturality theorem is proved from the explicit
  alternating symbol via determinant covariance and inverse-coframe
  contraction. The general result is
  `coordinateMetricHodgeTwoForm4_congruence_up_to_orientation`; the stronger
  `coordinateMetricHodgeTwoForm4_congruence_of_det_pos` removes the sign
  ambiguity for `det L>0`, and its canonical-seed specialization is exact.
   The detector wrappers prove directly, without assuming Hodge compatibility,
   that a positive-determinant selected coframe satisfying the Maxwell/frame
   gates passes `IsActualMetricHodgeCompatibleAt4`. Together with the finite
   determinant-`-1` reflection, Hodge is closed pointwise as an independent
   entrance premise. The upstream predicate itself now implies positive
   determinant. Coframe-entry continuity therefore retains positivity, and the
   fixed-choice neighborhood theorem re-derives exact Hodge compatibility at
   every point of the smaller open patch. Neither patch orientation nor the
   physical/reconstructed Hodge-field germ remains an independent premise.

The entrance implications and final integration steps are, in order:

1. **Choice-independent physical Ricci and scalar-jet entrance — complete on
   the stated regular patch.** `ChoiceIndependentActualMetricEMDRicciWitnessAt4` contains the
   physical scalar covector and metric dual, Maxwell Ricci residual, physical
   Ricci decomposition, Maxwell square law, and the explicitly generic
   pseudo-orthonormal Ricci eigenframe, but no detector choice. It now forces
   a literal finite scalar candidate equal to the physical covector up to
   global sign. `ChoiceIndependentActualMetricEMDRicciWitnessPatch4` packages
   the corresponding closed nonzero physical scalar field, and the fixed-
   probe cover, two-branch separation, constant-sign, and Frechet-derivative
   transfer theorems now force one literal detector closure obstruction to
   vanish. `ChoiceIndependentActualMetricEMDPhysicalPatch4` now extends this
   witness by genuine physical `C¹` Maxwell/Hodge fields, stress, Hodge, and
   exterior closure without introducing a detector choice.
2. **Complete Maxwell frame choice — complete for a fixed scalar branch.**
   The square law, trace, self-adjointness, index one, positive observer
   energy, coordinate specialization, and neighborhood persistence now
   construct every Maxwell frame index required by the finite detector. No
   rank, timelike-range, or preferred-frame witness remains as an input.
3. **Scalar probe choice — complete from invariant causal eigenline data.**
   `IsActualMetricScalarEigenlineCausalAt4` contains no detector choice, and
   `exists_eventually_actualMetricScalarProbeChoice` constructs both finite
   probe indices using only it, continuity, and the algebraic entrance.
4. **Hodge naturality and finite orientation — complete pointwise.** The
   explicit coordinate formula is covariant under the corrected true dual
   coframe up to determinant sign and is exactly natural when `det L>0`.
   The positive-orientation detector wrapper derives exact Hodge compatibility
   from the metric, Maxwell, and frame gates alone.
5. **Upstream selector composition — complete.** The same selected
   scalar branch now clears the literal closure, reconstruction, and complete
   Maxwell algebra gates:
   its overall sign cancels in the rank-one scalar tensor, matrix inversion
   recovers the physical metric-dual vector, and the physical Ricci
   decomposition becomes the detector's exact matrix obstruction. The
   physical Maxwell square law and self-adjointness then give the residual
   square and all four principal-projector identities.
   `exists_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch` composes
   this branch with the positive-energy frame and exact Hodge-orientation
   selectors into one raw choice passing every upstream metric gate.
   `exists_eventually_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch`
   then retains the same raw choice, scalar `±` germ, and frame signs on a
   smaller neighborhood, using only the added continuity of the two strict
   diagonal amplitudes and selected coframe entries. The open-patch wrappers
   produce an honest open `V` with upstream entrance everywhere; by
   `actualMetricPrincipalCoframeCandidate_det_pos_of_upstream`, its determinant
   is positive throughout.
6. **Finite generic-component selection — complete.** A nonzero component of
   the intrinsic active wedge forces the pulled scalar covector to be nonzero,
   selects a finite source index, and selects a finite wedge pair. The exact
   equivalence is
   `exists_actualMetricGenericFourthOrderComponentAt_withChannel_iff`.
   `isActualMetricFourthOrderDetectorCandidateAt_of_upstream_physical` then
   proves acceptance directly from the selected upstream choice, its physical
   channel, and that existential component. The former universal-genericity
   composition is retained only as a legacy logical lemma and is not a
   nonvacuous route to the theorem.
7. **Maxwell stress fibre, physical-germ derivation, and conditional
   nonemptiness — complete for the explicit patch package.** The scalar
   selector now retains a fixed
   `±` germ. The full algebraic Rainich fibre theorem is proved constructively:
   a skew two-form with canonical residual stress has only `01/23` amplitudes,
   their normalized values lie on the unit circle, arbitrary invertible
   adapted-frame changes preserve the statement, and the resulting duality
   coordinates are smooth and canonically generate the complexion one-form
   whenever the adapting frame and stress identities hold on a patch.
   The selected upstream coframe is now also proved to conjugate its actual
   Maxwell residual to `diag(-q,-q,q,q)`, and hence every physical skew form
   with that stress lies in the canonical duality orbit in the detector's own
   frame. The quotient-germ derivative bridge is also closed: local physical channel
   equality makes the literal quotient field locally equal to
   `a(c²-s²)`, so equality of actual Frechet derivatives is automatic.
   Separately, eventual equality of two genuine `C¹` matrix fields forces
   equality of their stored first jets, and the paired transfer theorem carries
   both physical EMD exterior equations to the reconstructed rotated seed jet.
   `NorthStarComposition.lean` now performs the formerly missing upgrade: on a
   smooth upstream patch (whose positive determinant follows from upstream),
   reconstructed stress gives smooth
   duality coordinates pointwise and the physical metric-Hodge relation fixes
   the partner with the same complexion. It derives both field germs and then
   composes first-jet transfer, physical EMD closure, active-wedge channel
   selection, and direct acceptance. The resulting theorem returns `a²`, and
   its Kaluza specialization returns `3`. Scalar reversal sends `a` to `-a`
   while preserving the invariant output.
8. **Invariant EMD physical packaging and sign-aligned composition —
   complete.** `InvariantEMDDetectorComposition.lean` introduces the
   detector-choice-free physical patch, derives detector residual stress,
   intersects the selected scalar and upstream germs into an honest open
   patch, and handles the two scalar orientations by coupling `a` or `-a`.
   `InvariantEMDEndToEnd.lean` composes the finite upstream selector and
   proves one accepted metric-only output equals `a²` (`3` for Kaluza).
9. **Selected regularity and physical activity — complete as ingredients.**
   `ActualMetricDetectorRegularity.lean` derives `C²` regularity of the
   selected coframe and positive magnitude from conventional `C²` data for
   `g`, the selected residual, and `qSq` under upstream entrance.
   `InvariantEMDRegularityEndToEnd.lean` uses those results in the invariant
   composition. `PhysicalComplexionInvariant.lean` independently constructs
   the choice-free physical complexion one-form, derives the source-free
   physical effective channel, and identifies detector activity exactly with
   the invariant physical Maxwell-complexion/stress condition. Do not
   reintroduce these as bespoke assumptions.
10. **Pointwise accepted-set confluence — complete on the sharp generic
    locus.** `InvariantEMDConfluence.lean` proves that any pointwise member of
    the finite accepted set equals physical `a²` when its scalar probe pair
    satisfies `¬(O_false=0 ∧ O_true=0)`, together with the displayed ordinary
    local regularity and admissible-probe hypotheses. Any two such survivors
    therefore agree. Without unique closure, both relative-sign branches may
    close, so unconditional identifiability is unsupported.
11. **Final invariant composition — complete.** The physical-active end-to-end
    theorem combines conventional selector/regularity data with one
    choice-free physical activity premise. Only selected-residual `C²` remains
    in its callback, and the conclusion is a metric-only accepted output `a²`
    (`3` in the Kaluza corollary).
12. **Complete exact routing and manuscript statement — active.** An
    adversarial routing audit proved that the original generic helical point
    does *not* pass the full finite detector: its shared timelike scalar
    radicand gate fails, so every raw choice is rejected. The replacement
    interior point passes the exact prefix through literal scalar
    reconstruction and the selected first-jet closure obstruction; the
    remaining gates are explicitly uncertified.
    Present nonemptiness together with per-survivor unique-closure correctness
    without suppressing the explicit regularity and admissible-probe scope.

No other research thread may displace these implications.

## Next gate: the finite-jet converse

Only after the entrance theorem closes:

1. test the reconstructed relations
   `dB = 2A(eta-(B/2)Jv)` and `d(A²+B²)=0`;
2. determine whether a fourth-order integrability reformulation exists;
3. if not, state the converse cleanly at metric order five;
4. integrate the complexion, reconstruct the physical Maxwell form with the
   convention-fixed `√2`, prove the full EMD realization, and compose it with
   the existing uplift/orbit theorem.

## Input and claim discipline

Detector acceptance may take only the metric, explicit generic hypotheses,
finite curvature jets, and vanishing obstruction equations. It may not take
an independently supplied scalar, Maxwell field, coupling, complexion,
preferred frame, `EMDEquations`, or EMD realizer. Such objects may occur only
as reconstructed outputs or as witnesses in the correctness direction.

The third-order no-go is presently a theorem about the complete first
curvature-seed channel system. It must not be advertised as a universal
statement about every natural metric three-jet invariant without an
additional formal jet-space completeness theorem.

## Focus rules

Until the two gates above close, defer:

- null, zero-trace, collision, and repeated-root branches;
- global bundle topology and new exact-solution searches;
- extra coordinate/uplift infrastructure;
- manifold-library migration;
- multipoles, waveforms, phenomenology, and laboratory applications.

Every theorem change must remove a forbidden input, close one displayed
implication, prove choice independence, or pass a required discriminatory
test. Theorem count and phase-checklist completion are not progress metrics.

## Publication outcomes

- **Strong detector paper:** active-regular finite-coordinate nonemptiness, physical
  correctness, confluence, the sharp channel-level third-order obstruction,
  fourth-order coupling recovery, and exact tests; full nonlinear-coordinate
  covariance remains an explicit upgrade.
- **Landmark paper/result:** the full finite-jet necessary-and-sufficient local
  Rainich–Kaluza recognition and uplift-orbit theorem.
- **Fallback:** the already-proved pointwise centralizer ambiguity plus exact
  zero/one/two differential scalar classifier.

Priority language remains “we are unaware of” until the literature audit is
confirmed by specialists in Rainich theory, EMD geometry, and exact solutions.
