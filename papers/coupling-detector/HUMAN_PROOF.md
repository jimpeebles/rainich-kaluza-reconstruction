# A fourth-order EMD coupling detector and a third-order no-go

Date: 2026-08-12  
Status: end-to-end proof draft for the detector paper

> **Current formal boundary.** The channel theorem, transported-seed
> nonemptiness, complete metric-only upstream selection, and the constructive
> Maxwell stress-fibre theorem are machine checked. Conditional actual-metric
> nonemptiness is now machine checked too. On a smooth
> upstream patch, reconstructed stress and the physical metric-Hodge relation
> derive the physical/reconstructed Maxwell/Hodge field germs; genuine `C¹`
> first jets, EMD closure, scalar continuity, and an active wedge then produce
> a finite accepted choice with output `a²`, or `3` at Kaluza coupling. The
> same selected scalar/frame/orientation choice now promotes to an honest open
> upstream patch under explicit diagonal-amplitude/coframe continuity, and
> upstream itself implies positive determinant. The detector-choice-free
> physical EMD package, scalar/upstream open-patch intersection, and
> scalar/coupling sign alignment are now composed end to end, producing one
> accepted metric-only output `a²` (`3` for Kaluza) under explicit selected
> regular-locus hypotheses. Conventional `C²` regularity of `g`, the selected
> residual, and `qSq` now derives the selected coframe and magnitude
> regularity. A choice-free physical complexion covector
> `(C dS-S dC)/2` now derives the source-free physical effective channel and
> identifies detector activity exactly with the invariant physical
> Maxwell-complexion/stress wedge; the active set is open under continuity,
> with no density claim. On the unique scalar-closure locus
> `¬(O_false=0 ∧ O_true=0)`, every pointwise accepted survivor is now proved to
> return physical `a²`, under the displayed ordinary local regularity and
> admissible-probe hypotheses. The final physical-active wrapper composes the
> conventional selector/regularity data with one choice-free activity premise
> and a callback supplying only selected-residual `C²`, and returns a
> metric-only accepted output `a²` (`3` for Kaluza). Exact benchmark routing,
> exposition/novelty validation, and the converse remain. A former
> universal-generic premise is withdrawn as vacuous because
> diagonal wedge components vanish.

## Status notation

- **[Lean]** means the finite-dimensional identity is machine checked in this
  repository and included in the axiom audit.
- **[Derived]** means the displayed differential-geometric calculation is
  written out here from the convention-fixed EMD equations.
- **[Open seam]** means that a stated converse or realization implication has
  not yet been derived from the intended invariant boundary. Necessity
  nonemptiness, selected regularity, physical-complexion activity, and unique-
  closure pointwise confluence are no longer placed in this category.

The central conclusion of this audit is a correction to the previous plan:
the physical coupling is not identifiable from the curvature-normalized
Maxwell channels at metric order three.  This failure is exact, not a defect
of the selected probes.  There is a one-parameter shear kernel.  Constancy of
the physical coupling breaks that kernel at metric order four on the generic
branch, yielding an explicit, choice-independent formula for `a²`.

## 1. Convention and scope

Work on an oriented four-dimensional Lorentzian patch `(U,g)` with signature
`(-,+,+,+)`.  The action convention is

```text
L = sqrt(-g) [ R - (1/4) exp(a phi) F_mn F^mn
                 - (1/2) d_m phi d^m phi ].
```

Put

```text
v = d phi,
calF = exp(a phi / 2) F,
H = calF / sqrt(2).
```

The extra constant normalization is essential: the Ricci residual is the
ordinary Maxwell stress of `H`, whereas it is one half of the ordinary
Maxwell stress of `calF`. The field equations used below are

```text
Ric_mn = H_mr H_n^r - (1/4) g_mn H^2
         + (1/2) v_m v_n,                              (1.1)
d H = (a/2) v wedge H,                                 (1.2)
d (*H) = -(a/2) v wedge (*H),                          (1.3)
box phi = (a/2) H^2.                                   (1.4)
```

The Kaluza value in this normalization is `a²=3`.  The proof concerns the
simple-spectrum, non-null Maxwell, nonzero scalar-covector branch.  It does
not classify the zero-trace, null Maxwell, null scalar-gradient,
repeated-root, or collision loci.

## 2. Curvature algebra and the finite scalar list

Raise one Ricci index and write the mixed endomorphism as

```text
Rcal = S + V,
V = (1/2) v-sharp tensor v.
```

The Maxwell residual is trace free and obeys the Rainich square law

```text
S^2 = q^2 I,       q > 0.                              (2.1)
```

The scalar part satisfies

```text
V^2 = tr(V) V.
```

Eliminating `S=Rcal-V` gives the reconstruction equation

```text
Rcal V + V Rcal - tr(V) V = Rcal^2 - q^2 I.           (2.2)
```

**[Lean]** The noncommutative implication, the protected opposite roots, the
quartic factorization, and the rational formula for `q²` are proved in the
algebraic entrance layer.

On a simple-spectrum patch, the Lagrange spectral projectors split the
relevant two-root block.  Lorentzian rank-one factorization of (2.2) produces
two pointwise covectors

```text
v_plus  = alpha + beta,
v_minus = alpha - beta,                               (2.3)
```

modulo their common overall sign.  The relative-sign reflection commutes
with `Rcal`, so pointwise Ricci curvature cannot distinguish the two
candidates.

Their exterior derivatives are

```text
d v_plus  = d alpha + d beta,
d v_minus = d alpha - d beta.                         (2.4)
```

Hence exactly zero, one, or two candidates survive the requirement `dv=0`.
On a convex patch every survivor integrates to a local scalar potential,
unique up to an additive constant.

**[Lean]** The relative-sign no-go, the exhaustive zero/one/two closure
classifier, and local integration are proved. The finite metric-only detector
now constructs the actual mixed Ricci field, characteristic roots,
polynomial projectors, amplitudes, fixed-probe scalar covectors, and closure
obstructions directly from the metric.

**[Lean]** The finite projected-probe theorem now proves that, once the
physical normalized components lie in the two rank-one ranges with the
reconstructed amplitudes, the detector's sum/difference list contains their
metric-dual sum up to one global sign, independently of probe choice.

**[Lean]** The abstract physical implication is now proved. Pairing the
reconstruction equation with a pseudo-orthonormal Ricci eigenbasis forces the
two complementary component magnitudes, makes both protected components
vanish off `a+b=±2q`, and composes with arbitrary finite projected probes to
produce a detector branch equal to the physical covector up to global sign.

**[Lean]** The actual metric projector/probe instantiation is now proved. The
algebraic gate, causal rank-one eigenlines, and four-root polynomial formulas
produce finite coordinate probes and a literal stored detector candidate
equal to the physical covector up to global sign.

**[Lean]** A choice-independent genuine EMD Ricci witness now derives the
reconstruction equation, selects the scalar probes and one fixed `±v` germ,
clears the literal scalar closure/reconstruction/Maxwell gates, and composes
the Maxwell frame and Hodge orientation into a complete upstream raw choice.
Exact coordinate Hodge naturality for a positive-determinant selected coframe
is derived from the metric and Maxwell/frame gates without assuming Hodge
compatibility. After the physical-channel splice, pointwise all-survivor
equality is proved on the unique scalar-closure locus; the two-closed-branch
exceptional locus remains deliberately outside that claim.

## 3. The curvature-normalized Maxwell seed

For a surviving scalar branch define

```text
S = Rcal - V,
J = S/q.                                               (3.1)
```

Then `J²=I`.  Its `-1` eigenspace is a Lorentzian two-plane and its `+1`
eigenspace is a spacelike two-plane.  Choose a local oriented orthonormal
coframe `(e0,e1,e2,e3)` adapted to these planes and set

```text
E  = sqrt(2q),
F0 = E e0 wedge e1,
G0 = *F0 = E e2 wedge e3.                             (3.2)
```

The Maxwell stress of `F0` is exactly `S`. Every
Ricci-residual-normalized physical Maxwell field in this orbit has the form

```text
H  = c F0 + s G0,
*H = -s F0 + c G0,
c²+s²=1.                                              (3.3)
```

Locally write `c=cos(theta)`, `s=sin(theta)`, and

```text
omega = d theta.                                      (3.4)
```

**[Lean]** Existence of the canonical square root, its stress, the Hodge seed,
transport through a Lorentz coframe, smooth fixed-probe adapted frames, and
the local positive-cosine angle chart are proved. More strongly, the converse
stress-fibre theorem is now constructive: any real skew form whose stress is
`diag(-q,-q,q,q)`, `q>0`, has only `01/23` components with squared amplitude
`2q`, hence is a unit duality rotation of `(F0,G0)`. Arbitrary invertible
adapted-frame covariance is proved pointwise. Smooth normalized duality
coordinates are proved on a positive adapted patch where the form, coframe,
and coframe/stress identities hold smoothly. Differentiating their unit-circle
identity canonically produces `omega` and both complexion derivative equations
without choosing `theta`.
For the actual metric detector, the upstream projector gates now prove
directly that its selected (possibly orientation-reflected) coframe conjugates
the recovered residual to `diag(-q,-q,q,q)`. Thus every physical skew form
with that residual stress lies pointwise in the canonical duality orbit in
the detector's own frame. The explicit coordinate Hodge formula is natural up
to determinant sign and exactly natural for `det L>0`; its actual-metric
wrapper proves the selected positive coframe's exact Hodge equality directly
from the coframe metric and Maxwell/frame gates.

**[Lean]** Upstream entrance itself now implies `det L>0`. Moreover
`exists_eventually_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch`
performs the finite scalar/frame/orientation selection once at the base point
and reuses that same raw choice on a smaller neighborhood. It retains the
scalar `±` germ and four strict frame signs; continuity of the two strict
reconstructed diagonal amplitudes and of the selected coframe entries promotes
every upstream gate and positive determinant. The open-patch wrappers return
an honest open set containing the base point. Thus common positive upstream-
patch selection is no longer an open geometric premise.

**[Lean]** `NorthStarComposition.lean` closes the neighborhood composition
that these facts were designed for. Reconstructed stress supplies smooth
duality coordinates for the genuine physical `C¹` Maxwell field throughout a
smooth upstream patch. Exact Hodge naturality and the physical
relation `G=*gF` then force the physical Hodge field to be the reconstructed
rotated partner with the same complexion. Thus both field germs are derived
pointwise across the patch, and the existing germ theorem identifies their
stored first jets and transfers physical EMD exterior closure to the
reconstructed seed jet. With scalar continuity and an active wedge, the
composed theorem existentially selects a finite channel and returns `a²`; its
Kaluza specialization returns `3`.

### 3.1 Why the frame probes are not physical data

Two orthonormal frames adapted to the same ordered principal planes differ by
a block-diagonal `O(1,1) x O(2)` transition.  If their total orientation and
relative plane orientation agree, the oriented area factors on the two
blocks agree.  Therefore

```text
(F0',G0') = epsilon (F0,G0),       epsilon in {+1,-1}. (3.5)
```

The sign is locally constant on a connected overlap.  All seed values and
seed derivative channels acquire the same factor, while `J`, `v`, `A`, `B`,
and `a²` do not.

**[Lean]** `transportedSeedPair_principalFrameOverlap` proves the common
factor law.  The common-scale theorems in
`ComplexionCouplingSystem.lean` prove that the evaluated reconstruction is
unchanged by any common nonzero factor.  Thus the fixed probes select a local
representative of an intrinsic seed line; they are not an input to the final
scalar invariant.

## 4. Rotate the exterior equations back to the seed frame

Define the double-angle coupling components

```text
A = a(c²-s²) = a cos(2 theta),
B = 2acs     = a sin(2 theta).                         (4.1)
```

Differentiate (3.3), insert (1.2)--(1.3), and rotate the resulting pair by
the inverse of the matrix in (3.3).  A direct calculation gives

```text
dF0 = (A/2) v wedge F0 - omega wedge G0
      + (B/2) v wedge G0,                             (4.2)

dG0 = omega wedge F0 + (B/2) v wedge F0
      - (A/2) v wedge G0.                             (4.3)
```

The principal involution acts on covectors in the canonical frame by

```text
Jv = (-v0,-v1,v2,v3).                                 (4.4)
```

Because `F0` occupies the `01` plane and `G0` the `23` plane,

```text
(Jv) wedge F0 =  v wedge F0,
(Jv) wedge G0 = -v wedge G0.                          (4.5)
```

Consequently (4.2)--(4.3) depend on `omega` and `B` only through

```text
eta = omega + (B/2) Jv,                               (4.6)
```

and become

```text
dF0 = (A/2) v wedge F0 - eta wedge G0,                (4.7)
dG0 = eta wedge F0 - (A/2) v wedge G0.                (4.8)
```

This is the decisive normal form.

## 5. What the first seed derivatives determine

In the canonical frame write the independent three-form components in the
order `012,013,023,123`.  Equations (4.7)--(4.8) give

| channel | `012` | `013` | `023` | `123` |
|---|---:|---:|---:|---:|
| `dF0` | `(AE/2)v2` | `(AE/2)v3` | `-E eta0` | `-E eta1` |
| `dG0` | `E eta2` | `E eta3` | `-(AE/2)v0` | `-(AE/2)v1` |

Thus `eta` is read directly from four components.  If `v != 0`, at least one
of its components is nonzero and the remaining four equations determine a
unique `A`.  The unused components are compatibility obstructions.

**[Lean]** `canonicalComplexionCouplingChannels_injective` proves that, for
`E != 0` and `v != 0`, the complete channel map `(eta,A) -> (dF0,dG0)` is
injective.  `existsUnique_canonicalComplexionCoupling` converts compatible
channel data into a unique output. The explicit
`canonicalEffectiveOneFormFromChannels` and four
`canonicalCosineCandidateFromChannels` quotients require exact reproduction
of the complete raw channel pair, so every unused tensor component is an
obstruction. No evaluation probes or two-by-two probe determinant remain.

This theorem must not be misread as recovery of `(omega,a)`.  In a general
curvature seed it recovers exactly `(eta,A)`.

The scalar equation supplies an independent third-order check.  Since

```text
H² = -4q(c²-s²),
```

equation (1.4) is

```text
box phi = -2q A,
A = -(box phi)/(2q).                                  (5.1)
```

**[Lean]** `cosineCouplingFromScalarEquation_eq` verifies the final scalar
algebra.  In the detector, equality between (5.1) and the channel-derived
`A` is an obstruction, not an assumption.

## 6. Third-order no-go: the exact shear kernel

For every real function value `tau`, make the pointwise replacement

```text
B     -> B + tau,
omega -> omega - (tau/2) Jv.                          (6.1)
```

Equation (4.6) shows that `eta` is unchanged.  So are `A`, (4.7), (4.8), the
Einstein equation, and the scalar equation.  Therefore the complete
first-derivative field-equation data cannot distinguish these pairs.

**[Lean]** `canonicalFullComplexionCouplingChannels_shear_invariant` proves
the symmetry for every `E,v,omega,A,B,tau`.
`canonicalFullComplexionCouplingChannels_not_injective` proves that the map
from `(omega,B)` to the full first-order channel pair is never injective.

This result falsifies the old third-order detector claim.  It is stronger
than failure of a particular probe determinant: no choice or number of
linear evaluations of these channels can recover `B`, because the complete
three-forms are identical.  Since

```text
a² = A²+B²,                                           (6.2)
```

the physical squared coupling is also not identifiable from this data.

The jet-order statement is precise.  Ricci, the scalar candidates, `S`, `q`,
`J`, and the seed values use `j²g`.  Their first exterior derivatives and
the scalar wave operator use `j³g`.  At that order the field equations see
`A` and `eta`, not `B`.  This is a no-go for the first differentiated
Rainich/EMD system; it is not presented as a theorem about every conceivable
nonlocal or unrelated metric invariant.

## 7. Constancy breaks the kernel one derivative later

For a genuine EMD theory, `a` is a constant parameter.  Differentiate the
first equation in (4.1):

```text
dA = -2B omega.                                       (7.1)
```

Use (4.6) to eliminate the unobservable `omega`:

```text
dA + 2B eta - B² Jv = 0.                              (7.2)
```

Every term in (7.2) is metric-constructed through order four except the one
scalar `B`.  Wedge (7.2) with `Jv`.  The quadratic term disappears:

```text
dA wedge Jv + 2B eta wedge Jv = 0.                    (7.3)
```

For a coordinate pair `i<j`, put

```text
Delta_ij = eta_i (Jv)_j - eta_j (Jv)_i.               (7.4)
```

Whenever `Delta_ij != 0`, (7.3) gives the explicit quotient

```text
B_ij = -[ (dA)_i (Jv)_j - (dA)_j (Jv)_i ]
       / (2 Delta_ij).                                (7.5)
```

The detector does not silently trust one component.  It computes (7.5) for
every nonzero `Delta_ij` and retains a candidate only if all four components
of (7.2) vanish.  If two component choices survive, they agree.

The quantifier here is necessarily existential. The finite list also contains
diagonal pairs `(i,i)`, for which `Delta_ii=0` identically; therefore no
nonempty upstream family can make every raw component generic. Lean proves
the exact replacement:

```text
eta wedge Jv != 0
  iff some enumerated source/wedge component is generic.             (7.7)
```

The left side already forces `v!=0`, so no separate nonzero-source hypothesis
is needed. Since `eta=omega+(B/2)Jv`, it also satisfies

```text
eta wedge Jv = omega wedge Jv = dtheta wedge J(dphi).                (7.8)
```

Thus the true generic locus is independent of the hidden sine component and
of the coupling.

**[Lean]** `nextOrderSineCouplingEquation_eq_zero` derives (7.2) from
`dA=-2B omega` and (4.6).
`sineCouplingFromNextOrderComponent_eq` proves (7.5).
`nextOrderSineCoupling_unique` proves component-independent uniqueness under
`eta wedge Jv != 0`. `IsFourthOrderChannelCandidate` retains the full
first-channel and four-component next-order obstruction equations;
`acceptedFourthOrderChannelChoices` is the resulting finite set of at most
64 source/wedge choices.

The finite next-order detector value is

```text
aGeomSq = A² + B².                                    (7.6)
```

**[Lean]** `couplingSqFromDoubleAngleComponents_eq` proves the double-angle
identity `A²+B²=a²`.  `couplingSqFromNextOrderComponent_eq` proves that the
explicit quotient (7.5), inserted into (7.6), returns the physical `a²` on
every genuine constant-coupling channel satisfying the genericity condition.

This is a finite coordinate construction using metric derivatives through
order four: `A` is constructed at order three and `dA` at order four. Full
nonlinear-coordinate covariance of the accepted-set construction is not yet
proved. In `FourthOrderMetricDetector.lean`, `dL` and `dq`
are actual coordinate Frechet derivatives of the transported curvature-seed
fields, `A(x)` is the explicit complete-channel quotient, and `dA` is the
actual Frechet derivative of that constructed scalar field. Patch acceptance
on an open set proves that different valid source components define equal
`A` fields locally and therefore equal `dA`; combined with next-order
uniqueness, every accepted source/wedge choice returns the same `aGeomSq`.

## 8. Choice independence

The squared detector has the following transformation laws.

1. **Adapted frame and fixed probes.** On an overlap the seed pair changes by
   a common locally constant sign.  The channel equations acquire the same
   sign, while their unique `(eta,A)` output, `Jv`, (7.2), `B`, and `aGeomSq`
   are unchanged.
2. **Channel component.** Every nonzero component of `eta wedge Jv` gives the
   same `B`, because a solution of (7.2) is unique.
3. **Scalar orientation.** Under `v -> -v`, the equivalent EMD presentation
   has `a -> -a`.  Then `A -> -A`, `B -> -B`, while (7.6) is unchanged.
4. **Spacetime orientation.** Reversing the Hodge orientation reverses the
   sine convention and hence `B`, but not (7.6).
5. **Overall Maxwell sign.** `(F0,G0)->-(F0,G0)` multiplies all seed channels
   by `-1` and changes none of the reconstructed scalar outputs.
6. **Scalar additive constant and gauge potential.** These alter the field
   presentation but not `v`, the Ricci-residual-normalized seed channels, or the
   detector.

Items 2, 3, and 5 have direct finite-dimensional Lean support. The
channel-level transformation law in item 1 is proved, but full confluence of
all independently selected actual-metric frame germs is still downstream of
the physical splice. Item 4 is the same double-angle sign algebra. Item 6
follows directly from the use of `v=dphi` and `H`, rather than a chosen
potential.

## 9. Detector theorem: publication-safe statement

The result supported by the present proof is best split into two theorems.

### Theorem A: channel-level obstruction and recovery

Let `(F0,G0)` be a nonzero canonical non-null Maxwell seed pair, let `v != 0`,
and suppose a physical Ricci-residual-normalized Maxwell form is related to the seed
by a local unit duality rotation.  Then:

1. the complete first seed-derivative pair uniquely determines `(eta,A)`;
2. the map from the physical variables `(omega,B)` to that complete pair has
   the shear kernel (6.1), and is never injective;
3. if the physical coupling is constant and `eta wedge Jv != 0`, the next
   derivative determines `B` uniquely by (7.5);
4. the scalar (7.6) equals the physical `a²` and is independent of the
   component and adapted-frame representative.

**Status:** all four clauses are **[Lean]**. The formal proof now includes the
inverse duality-rotation calculation and the frame-covariant pullback of the
wedge channels, so genuine local EMD closure implies (4.7)--(4.8) directly.

### Theorem B: compiled active-regular necessity detector

Let `g` be a sufficiently regular metric on an oriented Lorentzian patch
satisfying the explicit
simple-spectrum, positive-`q`, nonzero-scalar, strict projector-sign, scalar
closure, channel-compatibility, and `eta wedge Jv != 0` conditions.  Apply the
finite curvature algorithm in Sections 2--7 to every surviving scalar
branch.  It returns a finite list of fourth-order scalars `aGeomSq`.

If the metric carries the packaged constant-coupling Ricci--exterior EMD
witness on this active regular locus, one returned branch satisfies

```text
aGeomSq = a².                                         (9.1)
```

The returned value is independent of scalar orientation, adapted principal
frame, fixed probes, Hodge sign convention, Maxwell sign, and the component
used in (7.5).  The Kaluza necessary selector is

```text
aGeomSq = 3.                                          (9.2)
```

**Status: compiled.** The finite metric-only constructor, actual Ricci/root/projector
entry, scalar germ, arbitrary-basis Maxwell frame, true coframe, coordinate
Hodge orientation, actual fourth derivative, scalar-orientation invariance,
source/wedge confluence, accepted-branch physical correctness, and Kaluza
selector exist in Lean. The choice-independent EMD Ricci witness now composes
these into one complete upstream metric choice. Under continuity of the two
strict diagonal amplitudes and selected coframe entries, the same choice,
scalar `±` germ, and frame signs persist on an honest open upstream patch;
upstream implies positive determinant throughout. At the transported
curvature-seed boundary, Lean proves genuine-EMD channel necessity,
nonemptiness, and output `a²`. At the actual-metric boundary,
`exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_patch_physicalHodgeFields`
proves conditional accepted-set nonemptiness and output `a²` from the explicit
physical patch package; its Kaluza specialization returns `3`.

The adversarial audit removed one false route: universal genericity over raw
channels is impossible because diagonal wedge choices vanish. The corrected
active-wedge theorem existentially selects a generic finite channel, and
upstream plus a physical channel now directly gives accepted-set membership.
Lean also proves the full pointwise Maxwell stress-fibre theorem and its
smooth-patch version: a genuine non-null physical two-form is constructively
a unit duality rotation in an adapted frame, with smooth coordinates whenever
the positive adapted-frame and stress identities hold throughout the patch.

The field-germ seam is now closed conditionally. The north-star composition
uses reconstructed stress to pull the physical field into the smooth duality
orbit on the selected upstream patch, then uses exact Hodge naturality and the
physical Hodge relation to derive both physical/reconstructed field germs.
Their first jets, EMD exterior equations at oriented coupling `a` or `-a`,
local canonical channel, literal quotient derivative, active finite channel,
and accepted output then follow from the existing theorems.

The invariant physical composition is now closed too.
`ChoiceIndependentActualMetricEMDPhysicalPatch4` packages the genuine physical
`C¹` pair, stress, metric-Hodge relation, and exterior closure without any
detector choice. The selected scalar-sign germ is intersected with the
upstream germ on one honest open patch. On the negative scalar branch the
composition replaces `a` by `-a`, so both branches return the same `a²`.
`InvariantEMDEndToEnd.lean` invokes the finite upstream selector and proves
that one accepted metric-only survivor returns `a²`, or `3` under Kaluza
normalization.

The selected regularity seam is now closed as a derived implication.
`ActualMetricDetectorRegularity.lean` follows the finite construction through
projected probes, Lorentzian pivoting, signed Gram--Schmidt, matrix inversion,
and the constant orientation reflection. On an upstream patch it derives the
selected principal coframe's `C²` regularity from conventional `C²`
regularity of `g`, the selected residual, and `qSq`; positivity of `qSq`
similarly derives `C²` regularity of the protected magnitude.
`InvariantEMDRegularityEndToEnd.lean` feeds those conclusions into the
invariant necessity composition.

The physical complexion seam is closed choice-freely too.
`PhysicalComplexionInvariant.lean` constructs the physical double-angle
scalars `C,S` from `F`, its metric Hodge partner, inverse metric, and `q`, and
sets

```text
omega = (C dS - S dC)/2.
```

It proves that this equals the ordinary `c ds-s dc`, is invariant under
adapted-frame change and simultaneous reversal of the physical pair, and
derives `IsActualMetricPhysicalEffectiveChannelAt4` without first selecting a
source. Combined with `InvariantActiveWedge.lean`, it proves detector activity
equivalent to the choice-free physical Maxwell-complexion/stress wedge,
including the scalar `±` orbit.

Finally, `InvariantEMDConfluence.lean` isolates the sharp condition

```text
not (O_false = 0 and O_true = 0).
```

On this unique scalar-closure locus, any raw choice belonging pointwise to the
finite accepted set returns the physical `a²`, under the stated conventional
local regularity and admissible scalar-probe hypotheses. Hence any two
survivors agree there. The condition may not be silently dropped: if both
relative-sign branches close, acceptance alone does not identify which branch
is the physical scalar germ, and unconditional identifiability is currently
false or unsupported. The final physical-active wrapper now performs the
necessity composition: conventional selector/regularity data plus one
choice-free activity premise, with only selected-residual `C²` in its
callback, yield metric-only accepted-set nonemptiness.

`InvariantEMDPublicationCorollaries.lean` packages the survivor hypotheses
explicitly and proves that, when the accepted set is nonempty and every
survivor carries its certificate, the complete finite output-value set is
exactly the singleton `{a²}`.

## 10. Why this is not yet the full local converse

At channel level the fourth-order construction is a necessary coupling
detector on genuine solutions, and its conditional actual-metric
nonemptiness theorem is now complete for the explicit positive physical patch
data. The fixed open upstream patch, positive orientation, invariant physical
packaging, scalar/coupling sign alignment, conventional regularity discharge,
choice-free physical complexion/effective channel, invariant activity gate,
and unique-closure pointwise confluence are proved. The repository still does
not prove the converse claim that every accepted metric branch comes from a
constant-coupling EMD solution.

After recovering `B`, define

```text
omega = eta - (B/2) Jv.                               (10.1)
```

For an actual angle and constant `a`, one also has

```text
dB = 2A omega,                                        (10.2)
d(A²+B²)=0.                                           (10.3)
```

Testing (10.2) by directly differentiating the reconstructed `B` may require
one further metric derivative.  There may be a fourth-order integrability
reformulation using the exterior derivatives of (4.7)--(4.8), but that has
not been proved and must not be assumed.  For a converse, reconstructed
matter fields must also be shown to satisfy the EMD equations without taking
an `EMDEquations` realizer as an independent input; the actual-Ricci/Hodge
upstream composition itself is already proved.

Accordingly the detector paper should lead with the no-go plus generic
fourth-order recovery theorem.  The full necessary-and-sufficient Kaluza
recognition theorem is a later corollary only after (10.2)--(10.3) and the
remaining realization seams close.

## 11. Degenerate next-order branch

The recovery formula excludes

```text
eta wedge Jv = 0.                                     (11.1)
```

Since `J` is invertible and `v != 0`, this means `eta` is pointwise parallel
to `Jv`.  Equation (7.2) then collapses to a scalar quadratic when `dA` is
also parallel to `Jv`, and can have zero, one, or two roots.  This locus is
mathematically interesting but is not needed for the generic theorem.  It is
listed as a separate branch rather than buried in a denominator.

## 12. Exact tests and falsifiability

The repository supplies four exact-arithmetic roles:

1. a nonzero boosted-black-string convention ladder with `aGeomSq=3` on a
   repeated-root branch;
2. an exact `a²=1` EMD black-hole control that returns `1` and fails the
   Kaluza selector;
3. a simple-spectrum helical Kaluza reduction with exact EMD residual zero
   and physical-channel `aGeomSq=3`; the original point is outside the
   complete detector's causal scalar branch, while a replacement point has a
   certified passing scalar-prefix through literal first-jet closure only;
4. a paired second-jet near miss preserving the point metric, first jet,
   Lorentz signature, and simple spectrum while failing a named algebraic
   obstruction.

These tests validate conventions and selectivity.  They do not replace the
fourth-order theorem, and none is a newly discovered exact Kaluza spacetime;
the helical example is a reduction of a known Ricci-flat seed. The next
validation upgrade is to finish the complete detector route at the replacement
helical point; no accepted-set claim follows from the physical channel alone.

## 13. Remaining proof obligations, in order

1. Route a positive active benchmark through the complete finite detector, not
   only equations (4.7)--(4.8) and (7.2).
2. Present the compiled necessity and certified singleton-output theorems and
   validate its novelty position with specialist review.
3. Prove full nonlinear-coordinate covariance or state the coordinate scope
   prominently in the paper.
4. Only then investigate whether the full converse closes at order four by
   integrability, or honestly requires order five. The converse splice must
   also restore the constant factor `F=sqrt(2) exp(-a phi/2)H`; omitting it
   preserves closure but gives the wrong Einstein normalization.

No degenerate classification, new exact solution, or additional uplift
infrastructure is on this critical path.

## 14. Novelty position

Classical Rainich theory reconstructs Maxwell fields from curvature up to
duality.  Separate metric geometrization results exist for scalar and Maxwell
matter, and generalized Rainich identities exist in higher dimensions and in
some scalar-tensor settings.  Electromagnetic duality orbits in
Einstein-Maxwell-scalar models are also known.

A focused literature search has not located the specific result proved here:
the exact shear non-identifiability of the EMD sine-coupling component in the
complete first curvature-seed derivative channels, together with its generic
one-derivative-higher quotient and the invariant `A²+B²`.  This is a
provisional novelty assessment, not a priority claim.  A paper should say
“we are unaware of” until a specialist literature review confirms it.
