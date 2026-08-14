# Kaluza arc plan: local metric-only recognition of the Kaluza sector

Date: 2026-08-14

Status: forward program plan for the recognition theorem that would complete
the Rainich--Misner--Wheeler geometrization question for the sector
distinguished by Kaluza reduction.  This file plans work and claims nothing.
When documents disagree, [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md) governs what
may be claimed, [`RESEARCH_PLAN.md`](RESEARCH_PLAN.md) governs the active
paper, and this plan governs only post-paper sequencing.  Except for the
zero-claim items marked in Section 11, nothing here begins before the active
paper's gates P1--P3.

Audit update, 2026-08-14: Section 2 now requires persistent full channel
acceptance, treats the fifth-order propagation law as the only new phase
hypothesis, and separates fixed-branch existence from cross-branch
uniqueness.  Compilable Lean artifacts now cover literal actual-metric
fixed-choice coupling-circle propagation, both explicit `sqrt(3)` half-angle
charts and their coordinate phase laws, the convention-normalized Maxwell
scaling and potential, the `C³` normal-coordinate contracted-Bianchi core,
the normal-coordinate matter Noether/Hodge factor-sign algebra, normalized
Maxwell-stress transport through the reconstructed coframe, and the literal
neighborhood Einstein/source identity.  A conditional pointwise
fixed-coordinate/fixed-choice recognition theorem also compiles, including a
derived scalar residual and a Ricci-flat local Kaluza germ.  The strongest
compiled endpoint is the `_of_preHodge` theorem in
`CoreSourceDerivedHodgeBridge.lean` (not the file
`SourceDerivedPointwiseKaluzaRecognition.lean`, whose representative still
stores the exterior-Hodge law).  At that endpoint Einstein is derived from
the staged source and exact trace reversal, the weighted Maxwell/Hodge law
is derived from the staged closed weighted flux and normal Hodge
differentiation, and the scalar equation is derived from contracted
Bianchi/Noether.  One Maxwell-side input survives inside the normal
matter-jet package: the rescaled exterior law recorded as
`NormalRescaledMaxwellBianchi` is assumed, never derived, although the
analogous Hodge-side derivation pattern
(`matrixHodgeExterior_of_closed_scaledFirstJet` from the core's closed
convention Maxwell field) appears to apply.  Deriving it is the cheapest
outstanding Lean item.  Beyond that, only the normal matter-jet package and
a compatible `C²` normal representative remain at that fixed-chart layer,
and no theorem yet constructs a normal chart (metric value $\eta$, first
jet $0$) from a general nonsingular point, so the endpoints cannot yet be
applied away from an already-normalized presentation.  The
accepted coframe data now imply componentwise `C²` regularity of the original
coordinate metric; the unsolved representative work is the `C²` scalar and
gauge fields plus construction of a compatible normal-coordinate germ.  The
normal matter package still records the exact
detector-residual/normal-residual identification and the two rescaled Maxwell
first-jet identities used by the Noether argument;
it is not the invariant unconditional recognition theorem K-B/K-C target.
None of K-A through K-F is complete or enters the claim ledger.

## 1. Objective and shape of the program

One theorem closes the arc:

> **Target (arc theorem, v1, local).**  On the active, non-null,
> simple-spectrum branch, an explicit finite list of curvature conditions on
> a four-dimensional Lorentzian metric, using metric derivatives through a
> fixed finite order, is necessary and sufficient for the local existence of
> Einstein--Maxwell--dilaton fields at the Kaluza coupling $a^2=3$, unique
> up to the stated presentation orbit, whose convention-fixed uplift is a
> local Ricci-flat five-dimensional vacuum.

Three structural facts shape everything below.

1. **Recognition does not route through Cartan--Kähler.**  In the converse
   direction the matter fields are constructed explicitly from curvature and
   the field equations are verified by differentiating identities.  This
   lives at finite regularity and is independent of the EMD involutivity
   proposition.  The audited-pending lemma guards only sharpness -- the
   order-three lower bound -- so the specialist audit runs in parallel and
   is never on the critical path of the arc theorem itself.
2. **Covariance is constitutive.**  A chart-dependent recognition statement
   does not close an arc about geometry.  Gate E of
   [`ADVERSARIAL_REVIEW_RESPONSE.md`](ADVERSARIAL_REVIEW_RESPONSE.md) stops
   being optional hardening and becomes part of the theorem statement.
3. **The degenerate strata contain the textbook spherical solutions.**
   Spherical symmetry forces repeated Ricci roots, so the committed boosted
   string and GMGHS controls lie outside the current generic branch.  The
   helical Kaluza oracle is already active and simple-spectrum.  Arc v1 may
   be stated on the active branch, but the repeated-root stratum must follow
   before any "recognition of Kaluza spacetimes" language is applied to the
   textbook spherical examples.

## 2. Draft target statement and expected jet order

Conventions are those of [`EMD_CONVENTION.md`](EMD_CONVENTION.md); the
metric-constructed objects $v$, $J$, $H_0$, $\eta$, $A$, $B$ are
the compiled detector fields.  The anticipated hypothesis tiers are:

- **Algebraic entrance (metric order two).**  The existing pointwise
  entrance, stated invariantly: Lorentzian signature, self-adjoint mixed
  Ricci with the labeled simple real spectrum, positive non-null
  reconstructed Maxwell magnitude, causal scalar eigenline data, and the
  Kaluza polynomial obstruction.  This is only the preliminary algebraic
  tier; the reconstruction, Maxwell-projector, Hodge, and strict frame gates
  in `IsActualMetricUpstreamEntranceAt4` remain part of the persistent tier
  below.
- **Persistent entrance and first closure (metric orders two to four).**  On
  a sufficiently small open patch, one fixed finite raw detector choice must
  satisfy the full upstream entrance and reproduce every component of both
  seed-channel identities, not only the quotient components used to define
  $A$ and $B$.  In addition:


```math
dv = 0,
```


  together with the constancy equation already used by the detector,


```math
dA + 2B\eta - B^2 Jv = 0 .
```


- **Phase propagation (expected metric order five).**


```math
dB = 2A\Bigl(\eta-\frac B2\,Jv\Bigr).
```


  Because the constancy equation is
  $dA=-2B(\eta-(B/2)Jv)$, the two phase laws give
  $d(A^2+B^2)=0$, the coupling square is constant on the patch and the
  Kaluza selector reduces to the single pointwise equality $A^2+B^2=3$.
  After shrinking into one half-angle chart, lift $(A,B)/\sqrt3$ to
  $c^2+s^2=1$.  Differentiating this algebraic lift gives
  $dc=-s\omega$, $ds=c\omega$, where
  $\omega=\eta-(B/2)Jv$.  Thus $d\omega=0$ and a local angle are
  consequences rather than separate hypotheses.

- **Optional unique-branch gate.**  The exclusion


```math
\neg\bigl(O_-=0\wedge O_+=0\bigr)
```


  is not needed for existence from one fixed accepted branch.  Retain it
  only for confluence or uniqueness across the two scalar branches.

**Expected order.**  $B$ consumes the metric four-jet, so its propagation
law spends one further derivative.  The working expectation is therefore
that the recognition system closes at metric order **five**: identifying
$a^2$ is fourth order, while phase propagation is fifth.  The separate
closure test for $\eta-(B/2)Jv$, which would also be fifth order if imposed
directly, is redundant after the local half-angle lift.  This mirrors
classical Rainich, where algebraic conditions are joined by a differential
condition on the complexion gradient.  Whether order four already suffices
for recognition is open; neither optimality nor sufficiency of order five
may be claimed until settled.

**Conclusion of the target theorem.**  On a possibly smaller patch there
exist $\phi$ with $d\phi=v$, a local angle $\theta$ with
$d\theta=\eta-\frac B2 Jv$, the rotated physical field
$H=\cos\theta\,H_0+\sin\theta\,(*H_0)$, and
$F=\sqrt2\,e^{-\sqrt3\,\phi/2}H$ with a compiled gauge potential, such
that $(g,\phi,F)$ solves convention EMD at $a=\sqrt3$.  For one fixed
persistent accepted branch, the reconstructed presentation orbit is up to
the duality/scalar sign, the
$\phi$-shift/fiber-radius modulus, and Maxwell gauge (anchors:
`constantDuality_emd_iff_sign_of_active`, `equivalentUnder_dilatonShift`,
`equivalentUnder_gauge`, `equivalentUnder_iff_compatible`); and the
convention uplift is locally Ricci flat by `intrinsicRicciFlatAt_iff_emd`.
The converse direction -- every active-branch Kaluza reduction satisfies the
conditions -- reuses the compiled reduction equivalence.

The category is smooth with finite regularity (roughly $C^5$ metric data);
no analyticity is required on this path.  Uniqueness among arbitrary raw
detector choices is a further confluence/covariance obligation, not a
consequence of the cited fixed-branch orbit theorems alone.

## 3. K1 -- keystone lemma: contracted Bianchi for the actual Einstein tensor

Formalize $\nabla^\mu G_{\mu\nu}=0$ for the coordinate Einstein tensor
built from `actualCoordinateRicciCovariantField4` of a $C^3$ metric.  This
is a keystone Lean object in the program.  To force the scalar field equation
in the converse, it must be composed with a second formal deliverable: the
repository-normalized Maxwell- and scalar-stress divergence identities, or
equivalently the off-shell EMD Noether identity:

- Einstein holds by construction (the entrance forces the decomposition
  $\mathcal R=S+V$);
- Maxwell holds by construction (Section 2's closure tier plus the channel
  identities);
- Bianchi, Maxwell, and the matter-divergence identities then give
  $\bigl(\Box_g\phi-\frac{\sqrt3}4 e^{\sqrt3\phi}F^2\bigr)\,v = 0$,
  and $v\ne0$ on the active branch finishes the scalar equation.

This is the exact mirror of the Noether identity used in
[`ANALYTIC_EMD_REALIZATION.md`](ANALYTIC_EMD_REALIZATION.md), run in the
recognition direction.  The prerequisite infrastructure is already compiled:
the matrix-inverse chain rule
(`scalarFieldCoordinateFDeriv_matrixNonsingInv_apply4`), the composed-Ricci
derivative factorization
(`scalarFieldCoordinateFDeriv_actualCoordinateRicciCovariantField4`), and
the Schwarz-symmetry layer.  Suggested deliverables:
`actualCoordinateEinsteinField4` and
`actualCoordinateEinsteinField4_contractedBianchi`, followed by the exact
matter-divergence identity with the convention factors audited against
Section 3.4 of [`ANALYTIC_EMD_REALIZATION.md`](ANALYTIC_EMD_REALIZATION.md).
The first artifact now proves the algebraic cancellation and actual-field
factorization at a Minkowski normal-coordinate point.  Componentwise `C³`
metric regularity now supplies the genuine three-jet differentiability, all
required Schwarz symmetries, and composed-Ricci differentiability through a
new compositional proof.  The arbitrary-chart theorem is still open: it
needs either a direct connection-level second-Bianchi proof or
metric-three-jet/`CoordinateChangeJet4` transport.  On the matter side, the
normal-point scalar/Maxwell contractions, the raw Maxwell-stress variation,
and the Hodge-exterior-to-divergence conversion now compile with the audited
signs and factors.  `NormalEMDScalarEquationBridge.lean` composes them with
actual contracted Bianchi.  The honest metric-dependent inverse raising and
covariant lowering now reduce to the fixed-normal source variations when the
normal metric first jet vanishes, and an eventual neighborhood
Einstein/source equality differentiates to the exact raw matter-source
divergence.  `StagedEinsteinSourceBridge.lean` now constructs that
neighborhood equality from the staged Ricci entrance: it proves the exact
`sqrt(2)`/exponential Maxwell normalization, invariance of Maxwell stress
under unit duality rotation and coframe transport, and the resulting
covariant Einstein/source equality.  Its only abstract seed seam is
`StagedSeedEntranceAlignmentOn`; both concrete half-angle patches discharge
that alignment definitionally.  The remaining K1-facing work is to populate
the scalar/Maxwell first-jet and normal-residual identifications from the
constructed fields and a compatible normal germ, and to replace the
normal-coordinate Bianchi argument by an invariant or transported theorem.

## 4. K2 -- converse field-equation theorem

Derive on paper, then formalize: the Section 2 tiers imply local EMD fields.
The audited working derivation and a shorter staged theorem retaining an
explicit metric-constructed scalar residual are in
[`KALUZA_CONVERSE_DERIVATION.md`](KALUZA_CONVERSE_DERIVATION.md).
The paper derivation comes first because the principal mathematical risk of
the whole program is that the tier list is incomplete.  The skeleton is
$\phi$-integrability from scalar closure, propagation of $A^2+B^2$, a
local algebraic half-angle lift producing the phase fields, rotation of the
compiled seed pair, verification of the two
exterior equations as field identities through the existing germ/persistence
formulations, Einstein from the entrance identities, and the scalar equation
from K1.  The compiled radial-splice and potential modules supply a gauge
potential $\mathcal A$ with $d\mathcal A=F$ and its gauge orbit.  Only
after the full channel implications survive should the final Lean converse
statement be frozen.

`StagedKaluzaConverse.lean` now freezes the strongest honest intermediate
boundary.  For either explicit half-angle chart it constructs the paired
closed physical Maxwell/Hodge realization, the convention-normalized field
and gauge potential, and the exact entrance identities.  Full two-channel
Phase-III acceptance, the scalar-branch identification, and the scalar
residual remain visible inputs rather than being inferred from the accepted
detector quotient.

The next compiled layers substantially strengthen that boundary without
closing the invariant theorem.  `PhaseIIIChannelAcceptanceBridge.lean`
derives chart-specific Phase-III acceptance from the stored detector
channels.  `StagedEinsteinSourceBridge.lean` derives the pointwise and
neighborhood actual Einstein/source equations from the aligned entrance.
`ScalarResidualFreeStagedKaluzaConverse.lean` packages the exact normal
regularity and field-jet assumptions under which Bianchi/Noether derives the
scalar residual, and `PointwiseCoreKaluzaRecognition.lean` returns the full
local Ricci-flat uplift and presentation-orbit output at a selected point.
`CoreEinsteinSourceBridge.lean` removes the scalar-equation dependency from
the pointwise and neighborhood source identities.
`NormalEinsteinEquationBridge.lean` proves the exact four-dimensional trace
reversal, including the `exp(sqrt(3) phi)/2` normalization, while
`StagedEinsteinNormalGaugeBridge.lean` transports the actual metric, scalar,
and gauge germs to the product's genuine second jet.
`SourceDerivedPointwiseKaluzaRecognition.lean` then derives the normal
Einstein block rather than storing it, derives weighted Maxwell through the
normal Hodge bridge, and derives the scalar equation through Noether.  Thus a
pointwise fixed-coordinate/fixed-choice conditional recognition theorem is
compiled with no Einstein or scalar block assumed and the exterior-Hodge law
derived at the pre-Hodge endpoint; the rescaled Maxwell exterior law
(`NormalRescaledMaxwellBianchi`) is still an input carried by the matter-jet
package.  It remains conditional on a
compatible `C²` Minkowski normal/radial-gauge representative and the explicit
normal matter-jet/regularity package (including the detector-to-normal
residual formula and rescaled Maxwell first-jet identities).  Three named
Lean items close the visible gaps at this layer: derive
`NormalRescaledMaxwellBianchi` from the core's closed convention Maxwell
field by the Hodge-side pattern; prove normal-chart existence so the
endpoints apply at a general nonsingular accepted point; and consolidate the
recognition endpoint tower (`Staged`/`ScalarResidualFree`/`PointwiseCore`/
`SourceDerived`/pre-Hodge) into one canonical endpoint module, pruning
padding fields such as `presentation_orbit_complete`.
`NormalCoordinateHodgeFirstJet.lean` proves that differentiating the metric
Hodge star at a Minkowski normal point contributes no metric-variation term,
and `CoreSourceDerivedHodgeBridge.lean` uses this to derive the
representative exterior-Hodge law directly from the core's closed weighted
flux.  It neither constructs the `C²` representative from invariant metric
data nor proves chart-independent condition satisfaction.
`ActualMetricFixedChoicePhasePatchData.coordinateMetricContDiffTwo` removes
the metric-regularity part of that first task.  What remains is a normal-chart
germ together with `C²` regularity of the selected scalar and gauge
representatives; the present branch and closed-two-form interfaces supply
only the first-derivative data needed for `C¹` representatives.

## 5. K3 -- tensorial restatement and covariance

Two stages.  First finish the four-jet seam isolated in
`MetricFourJetFactorization.lean` (open item O2): equality of literal metric
four-jets forces equivalence of the full upstream entrance and equality of
the operational channel payload.  Second, restate the recognition conditions
invariantly -- the eigenvalue data, wedge conditions, and closure of
constructed one-forms are covariant in disguise; the probe/pivot enumeration
is scaffolding -- and prove **output covariance**: chart-independence of
condition satisfaction and of the recovered $a^2$ under the compiled
nonlinear coordinate-jet transformations.  Choice-by-choice correspondence
of raw detector choices is not required for the arc theorem.  The
publication term upgrades from "fixed-coordinate finite detector" only after
this lands.

## 6. K4 -- unconditional uplift and warp-constant uniqueness

Replace the conditional realizer: K2's outputs construct the fields that
`realize_emd` currently assumes, making the local Ricci-flat uplift an
unconditional corollary of recognition via the compiled equivalence
(`nonlinearLocalProductCoordinateRicciFlat_iff_emd`,
`intrinsicRicciFlatAt_iff_emd`).  Separately, quantify the warp ansatz and
prove the convention constants $c_1=-1/\sqrt3$, $c_2=2/\sqrt3$,
$c_3=1$ unique up to the stated presentation symmetries, so that
$a^2=3$ is derived rather than convention-checked.  This permanently
closes the honesty caveats recorded on C11 and C12.

## 7. K5 -- sharpness track (identical to the active paper's Gate G/P1)

The order-three solution-level lower bound stays conditional on the EMD
involutivity proposition until audited.  Package the rewritten realization
note plus the `vt3-emd-symbol-involutivity` certificate with a two-page
cover and approach two or three reviewer profiles in parallel: the
formal-theory/involution school, the author of the cited involutivity
theorem, and a geometrization-side relativist.  The compiled finite-jet
impossibility (`no_couplingSquare_identifier_on_activeFormalMetricThreeJet`)
is the unconditional floor if the audit stalls.  Sharpness never blocks
K1--K4.

## 8. K6 -- strata program

Priority order: the **repeated-root static stratum first**, since every
committed closed-form oracle (boosted string, GMGHS control) lives there and
Weyl-type methods may make it tractable by classical means; then null
Maxwell; then the $v=0$ and $F=0$ edges.  Each stratum gets its own
ledger rows before any recognition language extends to it.

One item is a result in either direction and deserves separate attention:
the both-branches-closed locus excluded by $\neg(O_-=0\wedge O_+=0)$.
Either prove rigidity there, or exhibit a metric with two inequivalent EMD
realizations.  The second outcome would be a striking standalone theorem.

## 9. K7 -- non-vacuity witness and oracles

The recognition pipeline needs a compiled inhabitant, not only symbolic
evidence, so Gate B gains urgency: a Lean instance of the physical-patch and
survivor interfaces, with the helical Kaluza patch as the target and a
simpler exact analytic local model acceptable first.  On the validation
side, add the missing generic rotating dyonic oracle (Rasheed--Larsen type)
as the first stress test of the fifth-order tier, and keep the existing
provenance and exact-arithmetic gates unchanged.  Gate C (independent
differentiation of the literal benchmark quotient) remains on this track.

## 10. K8 -- global layer (v2, explicitly out of scope for v1)

Gluing local uplifts into a genuine circle bundle: duality-phase holonomy,
the dilaton-shift/fiber-radius modulus, and flux quantization of $F$.  The
compiled overlap cocycle and presentation-orbit results
(`duality_overlap_cocycle`, `equivalentUnder_iff_compatible`) are the seeds.
Arc v1 is local in the Misner--Wheeler sense; every announcement must say
so.

## 11. Critical path and sequencing

Final critical path: **K1/Noether → K2 → K3 → K4 → paper II**.  The staged
K2 converse with an explicit scalar residual can proceed in parallel with
K1 and later discharge that extra condition through K1/Noether.  Other
parallel tracks: K5 (audit), K6 (strata), K7 (witness and oracles).
Deferred: K8.

The mathematical risk now concentrates in three places: supplying literal
detector persistence/regularity, constructing the compatible normal `C²`
field representative and discharging its remaining matter-jet/residual
normalization splice, and the arbitrary-coordinate covariance work of K3.  The
backend Einstein block and differentiation of the honest neighborhood
Einstein/source identity are compiled and are no longer separate risks.  The
fixed-choice propagation,
half-angle, normalized-stress, Bianchi, raw-stress, and Hodge-divergence
artifacts substantially narrow, but do not retire, the remaining risks.

Zero-claim items that may begin before the active paper's P1--P3 close,
because they add no claim surface: the K2 paper derivation, the K1 Bianchi
and Noether infrastructure, the pointwise phase-propagation algebra supporting
K2, and K5 reviewer outreach (which *is* P1).  Three further zero-claim Lean
items are now queued from the Section 4 audit: deriving
`NormalRescaledMaxwellBianchi`, the normal-chart existence lemma, and the
endpoint-tower consolidation.

## 11a. Gate crosswalk

Status of the gates from
[`ADVERSARIAL_REVIEW_RESPONSE.md`](ADVERSARIAL_REVIEW_RESPONSE.md), which is
now a dated snapshot; this table is the live tracker.

| Gate | Content | Now lives in | Status (2026-08-14) |
|---|---|---|---|
| A | Four-jet extensionality | K3 | Partially closed: entrance factors through the two-jet, acceptance/output through the operational payload, actual Ricci one-jets from four-jet equality; the derived-payload chain rule and upstream bridge remain open. |
| B | Compiled flagship inhabitant | K7 | Open; sharpened by the uninstantiated recognition representatives. |
| C | Direct benchmark quotient differentiation | K7 | Open. |
| D | Simplify all-survivor correctness | K3 (confluence) | Open. |
| E | Covariance | K3 | Open; constitutive for the arc theorem. |
| F | Kaluza converse without `realize_emd` | K2/K4 | Substantially advanced: staged and pointwise conditional endpoints compiled; representative construction, normal-chart existence, and the rescaled Maxwell derivation remain. |
| G | Formal-PDE specialist audit | K5 | Package ready (realization note + V5 certificate); outreach pending. |

## 12. Intended ledger rows (not yet claims)

| ID | Intended claim | Intended evidence class |
|---|---|---|
| K-A | Contracted Bianchi identity for the actual coordinate Einstein tensor of a $C^3$ metric, plus the normalized matter-divergence/EMD Noether identity used to derive the scalar equation. | Lean |
| K-B | The Section 2 condition tiers imply local EMD fields at $a^2=3$ for one fixed persistent accepted branch; a separate unique-closure corollary supplies the stated cross-branch orbit only after confluence is proved. | Lean, after a written derivation |
| K-C | Condition satisfaction and recovered $a^2$ are covariant under the supported nonlinear coordinate jets. | Lean |
| K-D | Unconditional local Ricci-flat uplift from a recognized branch; warp constants unique up to presentation symmetries. | Lean |
| K-E | Solution-level order-three lower bound. | Human + external until audited; compiled finite-jet floor already in place |
| K-F | Repeated-root stratum recognition. | Open |

No row enters [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md) before its artifact
compiles.

## 13. Prohibited upgrades

- No "recognition theorem" language before K-B **and** K-C both compile.
- No "Kaluza recognized from curvature" beyond the active branch and the
  strata with their own ledger rows.
- No global, bundle, or topology language in v1.
- "Order five" is an expectation: neither its sufficiency nor its
  optimality may be claimed until proved.
- Results conditioned on `realize_emd` keep the conditional label until K4
  lands.
- The arc theorem's independence from the involutivity proposition must not
  be presented as making K-E unconditional.

## 14. Stop rules

- If the K2 paper derivation finds the tier list insufficient, amend
  Section 2 before writing any Lean for K-B.
- No new exact-solution search except the rotating dyonic oracle of K7.
- No stratum formalization before the arc v1 statement freeze, except the
  repeated-root survey.
- Every landed result gets its ledger row before it is mentioned in the
  README or a manuscript.
- This plan defers to [`RESEARCH_PLAN.md`](RESEARCH_PLAN.md) until the
  active paper's P1--P3 close; only the Section 11 zero-claim items are
  exempt.
