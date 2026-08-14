# Kaluza converse derivation: audited fixed-choice skeleton

Date: 2026-08-14

Status: zero-claim working derivation for K2 of
[`KALUZA_ARC_PLAN.md`](KALUZA_ARC_PLAN.md).  This note freezes neither a
theorem statement nor a ledger row.  [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md)
continues to govern what may be claimed.

Compiled-status update, 2026-08-14: the fixed-choice construction now reaches
an honest neighborhood Einstein/source equality and a conditional pointwise
recognition theorem with the scalar residual derived by the normal
Bianchi/Noether bridge.  This is a fixed-coordinate, fixed-choice result with
an explicitly supplied compatible normal representative and matter jets.
The strongest compiled endpoint assumes none of the three EMD equation
blocks: its Einstein equation is derived from the core entrance, its weighted
Maxwell equation from exterior Hodge closure, and its scalar equation from
contracted Bianchi/Noether.  It
is not yet invariant, does not construct that representative from the metric
conditions alone, and therefore is not the unconditional recognition theorem
advertised by K-B/K-C.

## 1. What can be attempted now

The existing detector already supplies more than a value of `a^2`.  For one
raw choice accepted throughout an open patch, it supplies a metric-constructed
scalar covector `v`, principal reflection `J`, positive Maxwell seed `H0`,
effective phase form `eta`, cosine component `A`, sine component `B`, and the
complete first seed-channel identities.  Its fourth-order acceptance equation
is

```text
dA + 2 B eta - B^2 Jv = 0.                              (1.1)
```

Define

```text
omega = eta - (B/2) Jv.                                 (1.2)
```

Then (1.1) is exactly `dA = -2 B omega`.  A converse needs one new
fifth-order condition:

```text
dB = 2 A omega.                                          (1.3)
```

The scalar-branch closure `dv=0`, the complete seed-channel compatibility,
the active wedge, and (1.1) must also remain explicit.  They cannot be
replaced by the algebraic Ricci entrance alone.  Directly imposing
`d omega=0` would also consume the fifth metric jet because `omega` contains
the fourth-order quotient `B`, but that condition is redundant: the local
half-angle construction below derives it from (1.1) and (1.3).

The cleanest first formal target is fixed-coordinate and fixed-choice:

> **Staged converse (working form).**  Let `U` be a sufficiently small open
> convex patch and let one `ActualMetricDetectorChoice4` be accepted at every
> point of `U`, with the displayed denominators and regularity persistent on
> `U`.  Assume (1.3), the Kaluza selector `A^2+B^2=3` at one base point,
> and the metric-constructed scalar residual
> `div_g(v)+2qA=0`.  Then the reconstructed fields solve convention EMD for
> one orientation of `a=sqrt(3)` and admit the convention-fixed local
> Ricci-flat five-dimensional uplift.

This staged statement deliberately retains the scalar residual.  K1 plus the
matter-divergence identity should later prove that residual from Einstein and
Maxwell, removing it from the final hypothesis list.  The exclusion of the
both-scalar-branches-closed locus is not needed for this fixed-branch
existence statement; add it only to a later confluence or uniqueness
corollary.

## 2. Scalar and phase reconstruction

### 2.1 Scalar potential and coupling square

On an open convex patch, `dv=0` and the compiled Poincare theorem give
`phi` with `d phi=v`.  This use is already represented by
`exists_scalarPotential_of_closed`.

Equations (1.1)--(1.3) give

```text
dA = -2 B omega,
dB =  2 A omega.                                         (2.2)
```

They immediately imply

```text
d(A^2+B^2)
  = 2A dA + 2B dB
  = 0.                                                    (2.3)
```

Hence the base-point selector propagates on the connected patch.
`CouplingPhasePropagation.lean` compiles the pointwise product-rule
cancellation in (2.3), while `CouplingPhasePatch.lean` upgrades it to an
open-convex-patch constancy theorem.  Its detector-facing form fixes one raw
choice on the whole patch, retains the complete two-channel acceptance data,
requires actual differentiability of the reconstructed `A` and `B`, and
propagates the single base-point equality `A^2+B^2=3`.
`ActualMetricCouplingPhasePatch.lean` now instantiates that datum with the
literal metric detector.  It explicitly converts the detector's moving
principal-frame covectors back to coordinate Frechet derivatives and states
the conclusion directly as constancy of
`actualMetricFourthOrderCouplingSqCandidateAt`.

### 2.2 Local half-angle lift

Set `a=sqrt(3)` after choosing the scalar orientation.  Shrink around the
base point so that either `A != -a` or `A != a` throughout.  On the first
chart one may take

```text
c = sqrt((a+A)/(2a)),
s = B/(2ac).                                             (2.4)
```

The complementary chart exchanges the roles of `c` and `s`.  Equation (2.3)
gives

```text
c^2+s^2 = 1,
A = a(c^2-s^2),
B = 2acs.                                                (2.5)
```

Differentiate (2.5), use the unit-circle derivative and (2.2), and solve the
resulting two-by-two linear system:

```text
dc = -s omega,
ds =  c omega.                                           (2.6)
```

This algebraic half-angle route is preferable to assuming `d omega=0`.  It
constructs the phase fields directly and makes phase closure a consequence.
`LocalHalfAngleLift.lean` now packages both square-root charts, their
arbitrary-order smoothness on the strict chart domains, the reconstructions
(2.5), and the actual coordinate-derivative laws (2.6).
`ActualMetricHalfAngleSplice.lean` composes those charts with persistent
literal detector acceptance, the principal-frame `dB` equation, and one
base output equal to three; both `sqrt(3)` chart lifts now have compiled
coordinate phase laws.  If a literal angle is wanted, shrink once more and
lift the unit-circle pair `(c,s)` to `c=cos(theta)`, `s=sin(theta)`; that
optional circle-to-angle lift remains unpackaged, but it is no longer needed
to rotate the seed field.

Reversing the reconstructed scalar orientation sends the signed coupling to
its negative while preserving its square.  The existing
`kaluzaCoupling_has_positive_orientation` result then selects the convention
`a=sqrt(3)` without changing the metric-only selector.

## 3. Maxwell reconstruction

Acceptance of one fourth-order channel is stronger than acceptance of the
two quotient components.  By definition it checks exact reproduction of
all components of the seed equations

```text
dH0     = (A/2) v wedge H0 - eta wedge (*H0),
d(*H0)  = eta wedge H0 - (A/2) v wedge (*H0).             (3.1)
```

This full compatibility must be a patchwise hypothesis in the converse.  It
is encoded by `IsFourthOrderChannelCandidate` and must not be inferred from
the algebraic entrance or from the numerical output `A^2+B^2`.

Set

```text
H = c H0 + s (*H0).                                     (3.2)
```

Insert (1.2), (2.5), and (2.6) into (3.1), then differentiate (3.2).
This reverses the already-compiled seed calculation and
gives

```text
dH       =  (a/2) v wedge H,
d(*H)    = -(a/2) v wedge (*H).                          (3.3)
```

At the abstract exterior-jet level, the equivalence is already expressed by
`localPositiveQ_emdClosure_iff_seedChannels`.  The converse still needs a
field-level splice showing that the accepted metric germs supply its
derivative data uniformly on `U`.

Define the convention-normalized physical field

```text
F = sqrt(2) exp(-a phi/2) H.                             (3.4)
```

The product rules in `PhaseIVReadiness.lean` turn (3.3) into

```text
dF = 0,
d(exp(a phi) *F) = 0.                                   (3.5)
```

The legacy physical-field packages use the representative `F/sqrt(2)` in
part of this handoff.  `IsC1ClosedTwoFormOn.const_smul` now proves that
constant scaling preserves the entire closed `C^1` package, while
`PhaseIIIPhysicalMaxwellC1Realization.conventionNormalizedPhysicalMaxwell_closed`
specializes it to (3.4) and records the exact seed-component match.  The
matching `conventionNormalizedPhysicalMaxwell_gaugePotential` theorem scales
any legacy potential by `sqrt(2)` and proves that its curvature is the
convention-normalized field.

After shrinking to the star-shaped convex patch used by
`RadialPotentialSplice.lean`, (3.5) gives a gauge potential, denoted
`mathcalA` here to avoid collision with the detector scalar `A`, satisfying
`d mathcalA=F`.

## 4. Einstein and scalar equations

The upstream reconstruction obstruction gives the pointwise Ricci
decomposition

```text
Ric^mu_nu = S^mu_nu + (1/2) v^mu v_nu,                  (4.1)
```

and the principal seed is normalized so that the Maxwell stress of `H` is
exactly `S`.  With (3.4), (4.1) is the convention Einstein equation

```text
Ric_mn = (1/2) exp(a phi)
  (F_mr F_n^r - (1/4) g_mn F^2) + (1/2) v_m v_n.        (4.2)
```

There are two honest routes to the scalar equation.

### 4.1 Staged route: retain a scalar residual

Since

```text
exp(a phi) F^2 = 2 H^2,
H^2 = -4q(c^2-s^2),
A = a(c^2-s^2),
```

the scalar equation is exactly the metric-constructed condition

```text
box_g(phi) + 2qA = 0,                                   (4.3)
```

or `div_g(v)+2qA=0`.  This is expected to consume at most the metric
four-jet on the active branch.  Keeping (4.3) as a hypothesis gives a
shorter first converse and separates phase reconstruction from K1.

### 4.2 Final route: derive the residual

The final theorem should remove (4.3).  Contracted Bianchi for the actual
Einstein tensor and the Maxwell equations are not alone a compiled proof.
One also needs the exact matter-divergence identities

```text
div[exp(a phi) T_Maxwell(F)]
  = F . MaxwellResidual - (a/4) exp(a phi) F^2 v,

div[v tensor v - (1/2) g |v|^2]
  = box_g(phi) v,                                        (4.4)
```

with the repository's one-half normalizations.  Together they give the
off-shell Noether identity recorded as (3.8) in
`ANALYTIC_EMD_REALIZATION.md`.  Under (4.2) and (3.5),

```text
(box_g(phi) - (a/4) exp(a phi) F^2) v = 0.               (4.5)
```

The active wedge forces `v` to be nonzero, so (4.5) yields the scalar
equation.  `MatterStressDivergence.lean` now compiles the normal-coordinate
algebraic version of (4.4), including the factor/sign contraction and the
implication that vanishing total matter divergence forces the scalar
residual when `v != 0`.  It also proves that the raw first variation of the
Maxwell stress equals the alternating-form contraction.
`NormalMaxwellHodgeBridge.lean` derives the weighted Maxwell divergence with
the exact negative `a/2` sign from `G=*F`, `DG=*(DF)`, and the exterior
equation for `G`.  Finally, `NormalEMDScalarEquationBridge.lean` composes
those results with the actual `C^3` normal-coordinate contracted-Bianchi
theorem.  `EinsteinSourceFirstJetBridge.lean` now proves the complete
fixed-Minkowski scalar and Maxwell first variations, reduces the honest
metric-dependent raising/lowering derivative at a normal point, and
differentiates an eventual neighborhood Einstein/source equality to the
exact raw matter divergence.  `NormalEMDScalarEquationBridge.lean` consumes
that equality directly and forces the residual.

`StagedEinsteinSourceBridge.lean` now supplies the formerly missing
neighborhood equality.  It identifies
`H=exp(a phi/2)F/sqrt(2)` with the rotated Phase-III seed, proves that unit
duality rotation and coframe transport preserve its Maxwell stress, and
combines that result with the staged Ricci split to obtain both pointwise and
eventual actual Einstein/source equality.  The abstract alignment predicate
`StagedSeedEntranceAlignmentOn` says exactly that the Phase-III coframe and
positive magnitude are the detector's actual ones; both concrete half-angle
patches satisfy it by definition.  The remaining upstream work is therefore
the regularity and first-jet identification of the constructed scalar and
Maxwell fields with a compatible normal representative, not reconstruction
of the Einstein/source equality.

The two geometric identities underlying K1 are now compiled in the normal
frame:

1. contracted Bianchi for the actual coordinate Einstein tensor;
2. the Maxwell- and scalar-stress divergence/Noether identities.

What remains for K1 as an invariant deliverable is their arbitrary-coordinate
or transported formulation and the representative-level jet splice.

## 5. Uplift and the honest uniqueness boundary

Once (3.5), (4.2), and the scalar equation are assembled into the actual
`EMDEquations` field package, the existing backend gives the local uplift:

- `nonlinearLocalProductCoordinateRicciFlat_iff_emd`;
- `intrinsicRicciFlatAt_iff_emd`;
- `equivalentUnder_iff_compatible`.

The following orbit statements are already available for supplied branches:

- scalar potentials differ by a constant;
- gauge potentials differ by an exact one-form;
- active constant duality rotations reduce to the overall signs;
- compatible product presentations have the compiled warp/fiber/gauge
  orbit.

This does not yet prove uniqueness among every competing metric-derived raw
choice.  A final uniqueness statement needs patchwise survivor persistence,
choice confluence, and covariance, or must explicitly quantify only over
realizations of one fixed accepted branch.

There is now a compiled fixed-choice endpoint at precisely that latter
strength.  `ScalarResidualFreeStagedKaluzaConverse.lean` derives the staged
scalar residual from the explicit `FixedChoiceNormalEMDScalarDerivationAt`
package.  `PointwiseCoreKaluzaRecognition.lean` then proves
`exists_completePointwiseCoreKaluzaRecognition` (and detector-channel/Hodge
corollaries), returning EMD, intrinsic and nonlinear-coordinate Ricci
flatness, and the scalar/gauge/presentation orbits at one selected point.
`CoreEinsteinSourceBridge.lean` proves the same actual Einstein/source
identity before the scalar equation is known.
`NormalEinsteinEquationBridge.lean` proves the algebraic trace reversal from
that source to the backend Ricci source, and
`StagedEinsteinNormalGaugeBridge.lean` assembles the metric-second-jet,
scalar-first-jet, and normalized-Maxwell-value germ identifications.
Finally, `SourceDerivedPointwiseKaluzaRecognition.lean` returns the same full
uplift/orbit conclusion from a representative that stores no Einstein,
weighted-Maxwell, or scalar equation.  Those blocks are derived respectively
from the core source, exterior Hodge closure, and the normal Noether theorem.
`NormalCoordinateHodgeFirstJet.lean` and
`CoreSourceDerivedHodgeBridge.lean` go one step further: normal-coordinate
Hodge differentiation and the core's closed weighted flux derive the
representative exterior-Hodge law, so the strongest pre-Hodge endpoint does
not store it either.  The remaining conditional inputs are the existence of
the compatible `C²` normal/radial-gauge germ, its normal
matter-jet/regularity package, including the exact detector-to-normal
residual formula and the two rescaled Maxwell first-jet identities used by
Noether.  `CoreScalarResidualAlignment.lean` then derives the
product residual equality from those data; it is no longer a representative
field.
The accepted coframe identity and its `C²` frame regularity now also prove
componentwise `C²` regularity of the original coordinate metric.  The
remaining representative regularity is specifically `C²` for the selected
scalar and gauge potentials, plus construction of the compatible Minkowski
normal-coordinate germ; the current scalar-branch and closed-two-form APIs
only package enough derivative regularity for `C¹` representatives.
This pointwise result must not be described as invariant unconditional
recognition.

## 6. Jet-order audit

The direct dependency estimate on the active simple-spectrum branch is:

| Object or condition | Expected metric order |
|---|---:|
| `Ric`, `S`, `q`, `J`, `H0` | 2 |
| `v`, `dH0`, `eta`, `A` | 3 |
| `dv`, `dA`, reconstructed `B`, scalar residual (4.3) | 4 |
| `dB` (and the redundant direct `d omega` test) | 5 |

Thus order five remains a plausible sufficiency bound for the fixed-choice
converse, but it is not yet a theorem.  A separate `d omega=0` condition is
unnecessary after the local half-angle lift; if retained as a diagnostic, it
is fifth rather than fourth order.

## 7. Formalization sequence

The smallest dependency-respecting sequence is now:

1. supply persistence and differentiability to the now-compiled literal
   actual-metric fixed-choice propagation theorem;
2. use the now-compiled actual-metric `sqrt(3)` half-angle splice; an optional
   literal angle lift may be added separately;
3. use the compiled detector-channel equivalence to construct the physical
   Maxwell `C^1` package, convention `sqrt(2)` scaling, and gauge-potential
   orbit;
4. use the compiled staged entrance and normalized-stress bridge to obtain
   the neighborhood Einstein/source equality; this step is complete for both
   concrete half-angle charts;
5. construct the compatible normal-coordinate germ, upgrade the selected
   scalar and radial-gauge potentials to `C²`, and populate the remaining
   normal matter-jet/regularity package; metric `C²` is already derived from
   the accepted coframe data, and the Einstein,
   Hodge/weighted-Maxwell, scalar-residual, and Ricci-flat uplift assembly is
   now compiled from those inputs;
6. use the compiled pointwise recognition endpoint as the fixed-choice
   checkpoint, then prove arbitrary-coordinate transport and covariance;
7. only then strengthen from one fixed branch to the advertised uniqueness
   orbit.

This sequence can produce a meaningful fixed-coordinate sufficiency theorem
before the entire K1/K3 program is complete, without enlarging the active
paper's claim surface.
