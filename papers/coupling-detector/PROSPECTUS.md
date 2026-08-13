# Fourth-order EMD coupling detector: theorem prospectus

Status: revised after the active formal-jet audit, 2026-08-13

The full derivation is in [`HUMAN_PROOF.md`](HUMAN_PROOF.md).  This file is
the short theorem and assumption audit.

> **Current formal boundary.** Channel-level recovery, transported-seed
> nonemptiness, the finite generic-component selector, and complete
> metric-only upstream selection are proved. Conditional actual-metric
> nonemptiness is now also proved: on a smooth upstream patch,
> a genuine `C¹` Maxwell/Hodge pair with reconstructed stress, the physical
> metric-Hodge relation, EMD exterior closure, scalar continuity, and an active
> wedge produces a finite accepted choice with output `a²`; at Kaluza coupling
> it returns `3`. The same scalar/frame/orientation choice is now promoted to
> an honest smaller open upstream patch under continuity of the two strict
> diagonal amplitudes and coframe entries; upstream itself implies `det L>0`.
> Reconstructed stress, this upstream positivity, and the physical Hodge
> relation derive the physical/reconstructed field germs rather than assuming
> them. `InvariantEMDDetectorComposition.lean` now packages the conventional
> detector-choice-free physical EMD fields/stress/Hodge/closure, intersects the
> scalar and upstream germs into one open selected patch, and aligns coupling
> `a` or `-a`. `InvariantEMDEndToEnd.lean` composes the finite selector and
> returns one accepted metric-only output `a²` (`3` for Kaluza).
> `ActualMetricDetectorRegularity.lean` and the regularity end-to-end module
> derive selected coframe/magnitude `C²` regularity from conventional `C²`
> regularity of `g`, the selected residual, and `qSq` under upstream entrance.
> `PhysicalComplexionInvariant.lean` constructs
> `omega=(C dS-S dC)/2` choice-freely from the physical pair, proves its frame
> and simultaneous-sign invariance, derives the source-free physical channel,
> and identifies detector activity exactly with a physical
> Maxwell-complexion/stress wedge. `InvariantActiveWedgeOpenness.lean` proves
> this active set is open under continuity, without asserting density.
> `InvariantEMDConfluence.lean` proves that
> every pointwise accepted survivor returns physical `a²` on
> `¬(O_false=0 ∧ O_true=0)`, under the displayed ordinary local regularity and
> admissible-probe hypotheses. The final physical-active wrapper composes the
> conventional selector/regularity data with one choice-free activity premise;
> its callback supplies only selected-residual `C²`, and it concludes
> metric-only accepted-set nonemptiness with output `a²` (`3` for Kaluza).
> Exact benchmark routing, theorem exposition/novelty validation, and the
> converse remain. No claim of genericity for every raw component is made;
> diagonal wedge choices vanish identically.
>
> The lower-order statement is now realized by an active formal metric-jet
> continuum, not only by channel algebra. Every real `a` shares one explicit
> formal normal-coordinate metric three-jet satisfying the point
> Einstein/scalar equations and first Ricci prolongation, while the Maxwell
> first jet is injective in `a` and satisfies both exterior equations and
> point/first-jet Hodge compatibility.
> The product-rule coordinate-Ricci bridge and complete fixed-coordinate
> detector-germ extensionality are proved. This does not assert local EMD
> solutions, all-order integrability, or nonlinear-coordinate covariance.

## Target detector theorem

Let `(U,g)` be an oriented local coordinate patch of a four-dimensional
Lorentzian manifold.  Assume `g` is `C4` and that throughout `U`:

1. the mixed Ricci endomorphism lies on the stated real simple-spectrum
   branch with nonzero trace and positive reconstructed Maxwell magnitude;
2. the Lorentzian scalar-factorization radicands, spectral gaps, and strict
   projected-frame signs are nonzero;
3. at least one of the two curvature-reconstructed scalar covectors is closed
   and nonzero;
4. the complete curvature-seed derivative pair lies in the canonical
   effective channel range;
5. the generic next-order determinant `eta wedge Jv` is nonzero;
6. for the all-survivor conclusion, each admissible scalar probe pair lies on
   the unique-closure locus `not (O_false=0 and O_true=0)`;
7. the metric, selected residuals, and reconstructed `qSq` have the displayed
   ordinary `C²` regularity, with the strict probe/frame quantities continuous;
8. `U` is sufficiently small and convex for the local potential statements.

Item 6 is not needed merely to exhibit the physical survivor. It is the sharp
hypothesis that upgrades nonemptiness to pointwise correctness of every
accepted survivor. If both scalar branches close, the current theory does not
select one of them and makes no unconditional identifiability claim.

The finite enumeration no longer assumes that an individual projected
coordinate-basis vector is timelike. It selects a projected coordinate pair
and one of six metric-dependent algebraic pivot recipes. Lean proves that any
pair with negative two-by-two Gram determinant yields a timelike pivot and a
valid companion, and the resulting vector fields and principal tetrad are
smooth on their strict-sign patch. Lean now also proves that a rank-two
projector range containing a timelike vector in an index-one metric obtains
such a pair from any ambient basis, and directly obtains both strict
Gram–Schmidt signs. The coordinate-matrix bridge and persistence of one fixed
choice on a neighborhood are now proved by
`exists_smoothMatrixProjectedBasisLorentzianFrameSignsAt` and
`exists_eventually_smoothMatrixProjectedBasisLorentzianFrameSignsAt`.
Positive observer energy now derives the timelike negative range, while the
square law and trace derive rank two of both principal ranges. Lean composes
these facts into a complete locally persistent finite Maxwell-frame choice,
including the positive plane. The abstract physical scalar entrance and its
actual metric polynomial-projector, causal-line, finite coordinate-probe,
literal stored-candidate, fixed-sign germ, true-coframe, and Hodge-orientation
instantiations are now proved and composed into one upstream choice. That same
choice, scalar `±` germ, and frame signs now persist on an honest open upstream
patch under continuity of the two diagonal amplitudes and selected coframe
entries; upstream implies positive determinant everywhere on it. The
detector-choice-free physical EMD package and correlated coupling sign are now
composed with this selector. Conventional regularity now derives the selected
branch's `C²` coframe/magnitude data, and the choice-free physical complexion
construction derives its effective-channel identity and invariant active
condition. Neighborhood physical-channel transfer and the quotient-derivative
identity already follow from composition theorems.

Pointwise stress transfer into the selected actual frame is already closed.
The upstream projector gates prove that its coframe diagonalizes the recovered
Maxwell residual, and any physical skew form with that stress is then a unit
duality rotation of the detector seed. Positive-determinant Hodge naturality
is also exact, and upstream supplies the determinant sign.
`NorthStarComposition.lean` promotes these facts across the selected smooth
upstream patch and derives both physical/reconstructed field germs, their first
jets, and the physical channel. `InvariantEMDDetectorComposition.lean` then
supplies the detector-choice-free physical EMD patch, scalar/upstream open-
patch intersection, and correlated scalar/coupling sign; the end-to-end module
composes the finite selector. `InvariantActiveWedge.lean` supplies the
coordinate physical predicate and proves frame/sign invariance and cross-frame
confluence. `PhysicalComplexionInvariant.lean` supplies the missing
choice-free complexion/effective-channel construction and upgrades this to an
exact physical-active/detector-active equivalence before finite channel
selection. None of selected regularity, active-locus frame invariance,
physical packaging, sign alignment, positive-patch selection, the algebraic
orbit, Hodge identity, field-germ identity, first-jet uniqueness, or exterior-
equation transfer remains open.

Then `j4(g)` constructs a finite zero/one/two scalar-branch list.  Every
surviving fourth-order branch carries explicit effective channel variables
`(eta,A)`, a unique sine-coupling component `B`, and

```text
aGeomSq = A^2 + B^2.
```

The target conclusion is that, for every genuine constant-coupling EMD
solution in this generic class, the list contains its curvature branch and
`aGeomSq=a^2`. The transported-seed theorem, correctness of any actual-metric
branch carrying the physical channel, and conditional accepted-choice
existence from explicit physical patch data are proved. The fixed-choice open
upstream patch and its positive orientation are also proved. The conventional
invariant physical package, sign alignment, scalar/upstream patch
intersection, and end-to-end finite-selector composition are now proved. The
selected `C²` coframe/magnitude regularity is now derived from conventional
regularity data, and the choice-free physical complexion construction derives
the physical effective channel and exact active-gate equivalence. On the
unique scalar-closure locus, every pointwise accepted survivor is now proved
to return physical `a²`. The physical-active end-to-end wrapper now composes
these ingredients and proves accepted-set nonemptiness with physical output.
The Kaluza specialization is `aGeomSq=3`.

The active-component quantifier is existential. The detector enumerates all
raw components and rejects zero denominators. On
`eta wedge Jv != 0`, at least one enumerated source/wedge channel is generic;
not all channels can be generic because every diagonal wedge `(i,i)` is zero.
The identity `eta wedge Jv = dtheta wedge J(dphi)` shows that this active locus
is independent of the hidden `B` and of the coupling.

The theorem is a **necessity detector**, not yet a full local converse.
Testing that the reconstructed double-angle pair comes from one constant
coupling and an actual local complexion also requires

```text
dB = 2 A (eta - (B/2)Jv),
d(A^2+B^2)=0.
```

Directly differentiating the reconstructed `B` may raise the complete
recognition theorem to metric order five.  A fourth-order integrability
replacement has not yet been proved.

## Sharp lower-order obstruction

At metric order three the complete first seed-derivative channels determine
only

```text
A = a cos(2 theta),
eta = dtheta + (a sin(2 theta)/2) Jv.
```

They are invariant under the exact shear

```text
B      -> B + tau,
dtheta -> dtheta - (tau/2)Jv,
```

where `B=a sin(2 theta)`.  Hence the complete channel map is never injective
in `(dtheta,B)`, and `a^2=A^2+B^2` is not identifiable at that order.  This is
Lean-proved for the full three-form pair, so adding or changing scalar probes
cannot repair it.

The obstruction also has an explicit active formal metric-three-jet
representative. At a Minkowski normal point with `v=e^0+2e^2`, balanced non-null
curvature-normalized Maxwell form, and zero scalar Hessian, a common closed
and co-closed first-jet perturbation plus the coupling-dependent duality shear
gives an active physical complexion with wedge component `(0,2)=1`. The
duality shear is invisible to the Maxwell-stress first variation. Hence
`a=√3` and `a=1` have different Maxwell first jets and coupling squares but
one common symmetric `g2,g3`, satisfying the point Einstein/scalar equations,
first Einstein/Ricci prolongation, both exterior equations at the point, and
point/first-jet Hodge compatibility. The algebraic product-rule
`CoordinateRicciFirstJet` specialization identifies the displayed Ricci
prolongation with the formal coordinate-Ricci first-jet expression. This is a
collision in the truncated formal-jet class, not between actual local
solutions or actual smooth Ricci-field germs.

Constancy of `a` gives one derivative later

```text
dA + 2B eta - B^2 Jv = 0.
```

If `Delta_ij=(eta wedge Jv)_ij` is nonzero, then

```text
B = - (dA wedge Jv)_ij / (2 Delta_ij).
```

The full vector equation is retained as a compatibility obstruction, and
Lean proves that every valid component choice returns the same `B`.

## Assumption/output audit

| Datum | Final role | Current repository status |
|---|---|---|
| Lorentzian metric `g` | only detector input | the accepted set is metric-only; the necessity proof separately assumes a genuine physical EMD patch as its correctness witness |
| Ricci field through second derivative | constructed from `j4g` | actual coordinate metric jets, covariant Ricci, and mixed Ricci are definitionally constructed |
| labeled roots and projectors | local auxiliary construction | actual characteristic roots and four-root polynomial projectors are explicit metric formulas; the finite gate tests simple-root, eigenprojector, rank, and sign conditions |
| finite spectral probes | local trivialization only | idempotence plus trace one proves the scalar projector ranges are rank one; causal type selects coordinate projections, and normalized representatives differ only by sign. The choice-independent EMD Ricci witness derives the reconstruction equation and selects one literal candidate with a fixed local `±v` germ. Complete arbitrary-basis Maxwell-frame selection and persistence are also proved |
| scalar branches `v+`,`v-` | finite output candidates | zero/one/two closure classifier and local integration proved |
| residual `S`, involution `J`, seed line | metric-constructed candidates | scalar contribution, residual, principal projectors, and fixed-probe coframe are explicit metric formulas; the finite gate tests their square, self-adjointness, complementarity, and Gram signs |
| metric Hodge partner | metric-constructed obstruction | determinant covariance proves that the explicit coordinate formula is natural under the true inverse coframe up to orientation and exactly natural for `det L>0`. A finite reflection supplies the positive branch; detector wrappers derive exact Hodge compatibility, and upstream implies `det L>0` on the fixed open patch. Reconstructed stress and the physical Hodge relation derive the field germs. Conventional regularity derives selected coframe/magnitude `C²`, while the choice-free physical complexion construction derives the source-free effective channel and exact invariant active-gate equivalence |
| effective variables `(eta,A)` | third-order constructed outputs | full canonical channel map is probe-free and injective for `E!=0`, `v!=0` |
| physical `(omega,B)` at order three | forbidden interpretation | exact shear non-identifiability and noninjectivity proved |
| active formal metric `j3` | sharp lower-order witness in the displayed finite formal-jet class | `activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling` puts every real `a` over one fixed active formal metric three-jet while `activeAmbiguityMaxwellFirstJet_injective` distinguishes the matter jets; `exists_activeCommonFormalMetricThreeJet_kaluza_vs_one` specializes to `a²=3` and `a²=1`; `activeAmbiguity_kaluza_vs_one_firstChannel_ambiguous_nextOrder_separates` gives the same complete `(A,eta)=(0,e₂)` first channel and fixed finite next-order channel candidates `3` versus `1`; `coordinateRicciFirstJet_minkowski_zero` supplies the algebraic product-rule coordinate-Ricci first-jet bridge. No actual smooth-metric `fderiv` realization, local PDE realization, or all-order prolongation is claimed |
| formal witness spectrum | simple-real-spectrum certificate | `activeAmbiguityRicciSource_has_four_distinct_real_eigenpairs` proves exact roots `-1`, `1`, `(3-√65)/4`, `(3+√65)/4`, all pairwise distinct, with explicit eigenvectors. The remaining sharpness gap is local-solution/neighborhood realization, not repeated point spectrum |
| `B` | fourth-order constructed output | finite explicit quotient list, full compatibility equation, and uniqueness proved |
| `aGeomSq` | fourth-order coordinate output, invariant under the proved frame/sign/component transformations | the finite actual-metric set/value, actual `dA`, scalar-orientation invariance, source/wedge confluence, transported genuine-EMD necessity, upstream open-patch selector, and end-to-end physical-active theorem are proved. The physical active predicate is frame/sign invariant and exactly equivalent to the detector gate through a derived choice-free physical complexion/effective channel. The final wrapper has one physical-active premise and a selected-residual-`C²` callback and returns metric-only nonemptiness with output `a²`. Every pointwise accepted survivor equals physical `a²` on its probe-pair-specific `¬(O_false=0 ∧ O_true=0)` locus under conventional local regularity and admissible-probe hypotheses; unconditional confluence on the two-closed-branch locus and full nonlinear-coordinate covariance of the complete detector are not claimed |
| scalar equation | tested obstruction | gives the independent check `A=-box(phi)/(2q)` in the Ricci-residual seed normalization |
| physical EMD field | correctness-side witness only | its non-null stress fibre is constructively the unit duality orbit pointwise. The metric selector supplies the open upstream patch and positive determinant; reconstructed stress/Hodge derive the field germs and first jets. `ChoiceIndependentActualMetricEMDPhysicalPatch4` packages physical fields/stress/Hodge/closure without a detector choice, and the invariant composition aligns sign and returns one accepted output. `PhysicalComplexionInvariant.lean` constructs the invariant complexion/effective channel directly from that pair. A reconstructed full EMD realizer is needed only for the converse |
| five-dimensional germ | later corollary | conditional intrinsic uplift and converse already proved |
| detector coordinate germ | locality boundary | `actualMetricFourthOrderDetector_coordinateGerm_extensionality` proves equal coordinate metric germs have the same complete accepted set and raw-choice outputs; nonlinear chart covariance remains separate |

## Exact evidence

The exact suite contains a direct shear/fourth-order algebra regression, a
nonzero boosted-string convention ladder, an exact
`a^2=1` EMD rejection, a simple-spectrum helical Kaluza physical channel
returning `3`, and a paired second-jet near miss failing a named obstruction.
The complete-routing audit shows that the original helical point is rejected
by the detector's shared causal scalar gate. A replacement point passes the
entire exact pointwise upstream predicate and the convention-aligned
choice-free physical active wedge. Its selected fourth-order channel/output
has not yet been evaluated, so it is not yet a complete positive detector
oracle.

## Immediate proof sequence

1. **Complete:** formal first-order shear no-go and noninjectivity, together
   with an active common formal metric-three-jet at `a²=3` and `a²=1` and
   the product-rule coordinate-Ricci first-jet bridge.
2. **Complete:** formal next-order quotient, uniqueness, and `A^2+B^2=a^2`.
3. **Complete:** finite transported-seed list, actual `dA`, full component
   obstruction checks, and open-patch confluence.
4. **Complete at constructor level:** actual metric Ricci, roots, scalar
   candidates, residuals, principal coframes, and a fully explicit finite
   obstruction-filtered detector.
5. **Complete at the metric boundary:** coordinate metric Hodge construction,
   canonical convention check, scalar-orientation invariance, component
   confluence, accepted-branch physical correctness, and Kaluza value `3`.
6. **Complete at the transported-seed boundary:** duality-rotation inversion,
   wedge/pullback covariance, genuine-EMD channel necessity, generic finite-set
   nonemptiness, and output `a²`; also complete is the implication from an
   actual metric choice's EMD realization to physical correctness and `3`.
7. **Finite arbitrary-basis Lorentzian entrance complete:** a rank-two
   projector range containing a timelike vector obtains a negative-Gram pair
   from any ambient basis; six explicit recipes then give the timelike pivot
   and both strict frame signs. The recipe fields are smooth and the complete
   detector enumerates them instead of requiring a timelike individual
   coordinate projection.
8. **Fixed-choice open upstream patch, active component, and conditional
   physical splice complete:** the selected scalar/frame/orientation choice,
   scalar `±` germ, and frame signs persist on an honest smaller open patch
   under continuity of the two strict diagonal amplitudes and selected coframe
   entries. Upstream entrance implies positive determinant throughout. The
   corrected active-wedge theorem existentially selects one
   finite generic component, and direct physical-channel acceptance is
   proved. The full Maxwell stress fibre is constructively the unit duality
   orbit pointwise in arbitrary adapted coordinates, with smooth coordinates
   on a positive adapted patch satisfying the coframe and stress identities.
   `NorthStarComposition.lean` proves that reconstructed stress, the positivity
   supplied by upstream,
   and the physical Hodge relation derive the two physical/reconstructed field
   germs. With genuine `C¹` fields, EMD closure, scalar continuity, and an
   active wedge, its composed theorem produces an accepted choice with output
   `a²`; its Kaluza specialization returns `3`.
9. **Invariant physical composition and selected regularity complete:**
   the detector-choice-free physical fields/stress/Hodge/closure, open-patch
   germ intersection, scalar/coupling sign, and end-to-end finite-selector
   composition are proved. Conventional metric/residual/`qSq` regularity now
   derives the selected coframe/magnitude `C²` data. The choice-free physical
   complexion/effective-channel construction proves exact equivalence between
   physical activity and the detector gate.
10. **Pointwise confluence complete on unique closure:** every member of the
    finite accepted set returns physical `a²` under the displayed local
    regularity/probe hypotheses and its probe-pair-specific
    `¬(O_false=0 ∧ O_true=0)`. The physical-active end-to-end theorem now
    composes these ingredients into final nonemptiness. Complete the remaining
    selected fourth-order channel/output at the replacement exact point and
    present the theorem cleanly.
    Do not assert unconditional identifiability where both scalar branches
    close.
11. **Fixed-coordinate locality complete:** equal coordinate metric germs give
    the same accepted set and every raw-choice output. Do not promote this to
    nonlinear-coordinate covariance.
12. Validate the novelty position with specialist review and turn the compiled
    necessity result into the paper theorem statement.
13. Treat full local sufficiency separately; determine rather than assume its
   minimal jet order.

The zero-trace, null Maxwell, null scalar-gradient, repeated-root, collision,
and `eta wedge Jv=0` cases are explicit excluded branches, not claimed solved.
