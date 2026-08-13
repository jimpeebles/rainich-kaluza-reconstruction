# Result note: third-order obstruction, fourth-order recovery

Date: 2026-08-12

> **Current formal boundary.** Channel-level recovery and transported-seed
> nonemptiness are proved, and the metric-only construction now produces a
> complete upstream scalar/frame/Hodge choice. Conditional actual-metric
> nonemptiness is now proved: a genuine `C¹` Maxwell/Hodge pair on a smooth
> upstream patch, with reconstructed stress, the physical
> metric-Hodge relation, EMD exterior closure, scalar continuity, and an active
> wedge, produces a finite accepted choice with output `a²`; the Kaluza theorem
> returns `3`. The same selected scalar/frame/orientation choice is now
> retained on an honest smaller open upstream patch under continuity of the two
> diagonal amplitudes and selected coframe entries; upstream itself implies
> positive determinant. Stress plus that positivity plus the physical Hodge
> relation derive the physical/reconstructed field germs, their first jets,
> and the physical channel. The detector-choice-free invariant EMD physical
> package, scalar/upstream open-patch intersection, and scalar/coupling sign
> alignment are now composed. The end-to-end theorem applies the finite
> selector and produces one metric-only accepted output `a²` (`3` for Kaluza)
> under explicit selected regular-locus hypotheses. Conventional `C²`
> regularity of `g`, the selected residual, and `qSq` now derives the selected
> coframe/magnitude regularity. A choice-free physical complexion covector
> `(C dS-S dC)/2` now derives the source-free physical effective channel and
> makes the invariant physical Maxwell-complexion/stress wedge exactly
> equivalent to detector activity; this active set is open under continuity,
> with no density claim. On the sharp unique scalar-closure locus,
> every pointwise accepted survivor is proved to return physical `a²` under
> the displayed ordinary local regularity and admissible-probe hypotheses.
> The final physical-active wrapper now combines conventional selector/
> regularity data, one choice-free activity premise, and only selected-residual
> `C²` in its callback to prove metric-only accepted-set nonemptiness with
> output `a²`; the Kaluza corollary returns `3`. Exact complete-detector
> benchmark routing, exposition/novelty validation, and the separate converse
> remain.

The strongest coherent result in the repository has changed.  The former
evaluated two-channel constructor was mathematically correct in an aligned
gauge, but its physical interpretation was too optimistic for an arbitrary
curvature-normalized Maxwell seed.

## New result

Write the physical Ricci-residual-normalized Maxwell field
`H=exp(a phi/2)F/sqrt(2)` relative to the canonical principal-plane seed as

```text
H = cos(theta) F0 + sin(theta) (*F0).
```

Set

```text
A = a cos(2 theta),
B = a sin(2 theta),
eta = dtheta + (B/2)Jv,
```

where `v=dphi` and `J` is the normalized Maxwell residual involution.  The
complete first exterior channel pair determines `(eta,A)` uniquely whenever
the seed and `v` are nonzero.  It does not determine `(dtheta,B)`: for every
`tau`,

```text
B      -> B + tau,
dtheta -> dtheta - (tau/2)Jv
```

leaves the complete channels unchanged.  This makes the physical channel map
noninjective and rules out the previous third-order coupling claim.

For constant physical coupling,

```text
dA + 2B eta - B^2 Jv = 0.
```

If one component of `eta wedge Jv` is nonzero, then

```text
B = -(dA wedge Jv)_ij / (2(eta wedge Jv)_ij),
aGeomSq = A^2+B^2 = a^2.
```

Lean now proves explicit witness-free extraction of `(eta,A)` from raw
channels, exact reproduction of all unused components as obstruction tests,
the shear invariance and noninjectivity in `(dtheta,B)`, a finite 64-choice
fourth-order candidate set, the explicit next-order quotient, and the final
double-angle identity. It also constructs `dL`, `dq`, and `dA` by actual
Frechet differentiation of the transported curvature-seed fields. If two
source/wedge choices are accepted on an open patch, their `aGeomSq` outputs
agree. The formal development also constructs the actual mixed Ricci field,
characteristic roots and projectors, finite scalar and principal-frame
probes, residual, coframe, raw channels, and a fully explicit finite
metric-only accepted set. An explicit coordinate metric Hodge formula agrees
with the canonical Minkowski convention, is natural up to determinant sign,
and is exactly natural for a positive-determinant coframe. The detector's
positive-coframe wrapper derives exact Hodge compatibility without assuming
it. Scalar-orientation reversal leaves the squared
output unchanged. Every accepted branch satisfying the packaged genuine
constant-coupling channel predicate returns `a²`, hence returns `3` on the
Kaluza branch; any two accepted raw choices compatible with the same physical
coupling agree even when their scalar relative-sign and frame probes differ.
The formal implication no longer stops at that packaged predicate. Lean now
inverts the physical duality rotation, proves pullback covariance of the
one-form/two-form wedge channels, and derives the canonical physical channel
directly from genuine local EMD exterior closure. With `q>0`, a nonzero scalar
source, and `eta wedge Jv != 0`, the finite transported curvature-seed detector
is nonempty and every accepted branch returns `a²`. At the actual-metric
boundary, a genuine EMD realization of the fields constructed by a raw choice
implies the packaged predicate and hence the Kaluza selector `3`.
Moreover, the upstream algebraic/scalar/frame/Hodge gate is now separated
from the fourth-order channel gate: upstream entrance plus genuine EMD
realization for that same selected source, together with one nonzero
source/wedge component, constructs actual membership in the complete finite
metric-only accepted set and yields `aGeomSq=a²` directly.

## Adversarial correction and Maxwell stress fibre

The finite detector enumerates all source and wedge components, including
diagonal pairs `(i,i)`. Such a pair has identically zero wedge denominator.
Therefore a former conditional theorem whose premise required *every*
upstream raw choice to be generic was vacuous whenever an upstream choice
existed. That premise is no longer part of the research route.

The corrected statement is exact and existential. The intrinsic condition

```text
eta wedge Jv != 0
```

holds if and only if at least one enumerated source/wedge choice is generic;
the nonzero wedge already forces `v != 0` and hence supplies a source
component. Moreover,

```text
eta wedge Jv = dtheta wedge J(dphi),
```

so the active locus is independent of the hidden sine channel `B` and of the
coupling. Lean now proves the finite existential selector, direct acceptance
from an upstream choice plus a physical channel, and the resulting `a²`
output (including `3` on the Kaluza branch).

`InvariantActiveWedge.lean` gives this locus a choice-independent coordinate
form: `omega` has nonzero wedge with the cotangent action `Sᵀv` of the mixed
Maxwell stress. The predicate is unchanged by invertible coframe pullback or
scalar sign, and any two principal frames canonicalizing the same non-null
stress agree on it. On an upstream actual-metric branch, the coordinate
predicate is equivalent to the detector's extracted active gate once the raw
channel is identified with the explicit physical effective-channel form.
`PhysicalComplexionInvariant.lean` now supplies that bridge without choosing a
source. From physical `F`, its Hodge partner, inverse metric, and positive
stress magnitude it forms the physical double angles `C,S` and
`omega=(C dS-S dC)/2`, proves `omega=c ds-s dc`, and proves invariance under
frame changes and simultaneous `F,H` reversal. It derives the physical
effective-channel identity and proves exact equivalence between detector
activity and the choice-free physical Maxwell-complexion/stress condition,
including scalar orientation reversal.

The other major seam closed in this audit is the full non-null Maxwell
stress-fibre theorem. For `q>0`, every real skew two-form `F` satisfying

```text
MaxwellStress(F) = diag(-q,-q,q,q)
```

has exactly the canonical principal-plane form

```text
F = E e01 + B e23,       E²+B²=2q,
```

and hence lies in the unit duality orbit of the positive canonical seed.
The pointwise result is proved under arbitrary invertible adapted-frame
transport, not only in a pre-aligned chart. When the positive amplitude,
physical form, adapted coframe, and coframe/stress identities hold smoothly
throughout a patch, explicit normalized `01/23` components give smooth
duality coordinates; their unit-circle derivative canonically supplies the
complexion one-form without choosing an angle.
This is the constructive algebraic and analytic Rainich bridge needed for the
physical splice.

The quotient derivative no longer remains an independent assumption. Lean
proves that if the curvature channels equal the physical canonical channel on
a neighborhood and one fixed scalar source remains nonzero, then the
detector's literal quotient field is locally `A=a(c²-s²)`. Equality of actual
Frechet derivatives gives exactly the physical double-angle derivative.

The arbitrary-frame orbit now reaches the detector's selected metric frame
pointwise. From the upstream projector and frame gates, Lean proves that the
selected coframe conjugates the recovered Maxwell residual to
`diag(-q,-q,q,q)`. Therefore any physical skew two-form whose Maxwell stress
is that residual pulls back to a unit duality rotation of the canonical seed.
On the positive-determinant branch, the coordinate Hodge partner is exact.
`NorthStarComposition.lean` now performs the neighborhood upgrade: on any
smooth upstream patch, reconstructed stress gives smooth
duality coordinates and the physical Hodge relation fixes the partner with
the same complexion. The two physical/reconstructed field germs, first-jet
identification, and transfer of the physical exterior equations are derived,
not assumed. `ActualMetricScalarIdentifiability.lean` now supplies the same
fixed-choice open upstream patch, and upstream itself supplies the determinant
sign; positive-patch selection is therefore no longer open.

## Scientific interpretation

This is not a failed third-order proof patched by more probes.  It is a sharp
identifiability result:

- the metric three-jet reaches a genuine one-dimensional information barrier
  in the first differentiated EMD/Rainich system;
- one additional metric derivative breaks that barrier on the active locus
  because `a` is a constant theory parameter;
- the resulting scalar is the orientation-independent physical coupling
  square and selects the Kaluza value by `aGeomSq=3`.

The detailed derivation and theorem boundary are in
[`HUMAN_PROOF.md`](HUMAN_PROOF.md).

This result is a new identifiability theorem candidate, not a newly discovered
exact Kaluza spacetime. The helical Schwarzschild-string reduction is a
validation oracle built from a known Ricci-flat seed.

## What may be claimed now

The repository now contains a finite fourth-order list whose only detector
input is the actual metric, a genuine-EMD nonemptiness theorem at the
transported curvature-seed boundary, a complete metric-only upstream-choice
selector, the Maxwell stress-fibre theorem above, and a conditional
actual-metric accepted-choice theorem. Under its explicit physical patch
package, reconstructed stress, positive orientation, and the physical Hodge
relation derive the two neighborhood field equalities; genuine EMD closure
and an active wedge then give output `a²`, or `3` at Kaluza coupling. The
fixed raw upstream choice, its open patch, and positive determinant are now
proved. `InvariantEMDDetectorComposition.lean` now packages the physical `C¹`
fields, stress, Hodge relation, and closure without a detector choice,
intersects the scalar and upstream germs into one open selected patch, and
correlates scalar orientation with coupling `a` or `-a`.
`InvariantEMDEndToEnd.lean` composes the finite selector and proves one
accepted metric-only output equals `a²`, or `3` at Kaluza coupling. The
explicit conventional `C²` hypotheses on `g`, the selected residual, and
`qSq` discharge the selected coframe/magnitude regularity, while the physical
pair constructs the choice-free complexion/effective channel.
`InvariantEMDConfluence.lean` further proves
that any pointwise member of the finite accepted set equals physical `a²` on
`¬(O_false=0 ∧ O_true=0)`, with conventional local regularity and admissible-
probe hypotheses; hence all survivors agree on that locus. The exclusion is
sharp for the present argument because both relative-sign scalar branches may
close. `InvariantEMDPhysicalActiveEndToEnd.lean` closes the nonemptiness
composition with one choice-free physical-active premise and a callback that
supplies only selected-residual `C²`. The publication work now is exact
complete-detector routing and theorem exposition/novelty validation. The
repository does not yet prove the full local converse: reconstructing an
actual constant coupling and complexion requires the remaining relation for
`dB`, which may introduce a fifth metric derivative unless a fourth-order
integrability formulation is found.

The detector now enriches its finite coordinate-pair choices with six
metric-dependent Lorentzian pivot recipes. A Lean theorem proves that any
pair with negative Gram determinant contains a recipe producing a timelike
pivot and valid companion, including charts in which no individual projected
coordinate vector is timelike; smooth field-level construction is also
proved and integrated into the complete detector. A second theorem now proves
that a rank-two Lorentzian projector range selects a negative-Gram projected
pair from any ambient basis and therefore obtains both strict frame signs.
The coordinate-matrix specialization and local persistence are proved.
Positive observer energy, the Maxwell square law, trace, and self-adjointness
now construct the entire finite negative/positive Maxwell frame on a
neighborhood for any fixed scalar branch passing the metric Maxwell gate.
The scalar probes are now finite consequences too: projector idempotence and
trace one imply rank one, causal eigenline type selects a coordinate
projection on each line, the signs persist locally, and normalized choices
differ only by sign. More strongly, the projected-probe two-line theorem
proves that their finite sum/difference list reproduces the same metric-dual
covector orbit as arbitrary physical normalized representatives of the two
rank-one ranges, up to one global sign. The abstract physical entrance is now
complete as well: pairing the reconstruction equation with a generic
pseudo-orthonormal Ricci eigenbasis forces the reconstructed component
magnitudes, kills both nonresonant protected-root components, and composes
with the finite probes to return the physical scalar covector up to global
sign. The actual-metric projector/probe instantiation is now complete:
`exists_actualMetricFiniteProbeScalarBranch_eq_or_neg_of_physicalCovector`
uses the actual polynomial projectors and finite coordinate search and returns
one literal stored detector scalar candidate equal to the physical covector or
its negative. Arbitrary-chart upstream entrance, including scalar branch,
Maxwell frame, true coframe, and exact positive-orientation Hodge gate, is now
composed pointwise. Conditional complete nonemptiness and the quotient
derivative are composed in `NorthStarComposition.lean`; the same choice is now
promoted to an open upstream patch, with positive determinant implied by
upstream. The invariant composition modules now close conventional physical
packaging, sign alignment, scalar/upstream germ intersection, and end-to-end
single-survivor necessity. Conventional regularity now derives the selected
`C²` coframe and magnitude, while the choice-free physical complexion module
derives the effective channel and invariant activity gate. Pointwise all-
survivor correctness is proved on the unique scalar-closure locus. The final
physical-active theorem composes those facts into accepted-set nonemptiness.
The remaining publication work is to route the exact benchmark through the
full finite detector and present and validate the theorem's novelty.

## Publication route

The detector paper should be organized around the lower-order obstruction and
the higher-order recovery, with the existing zero/one/two scalar classifier
and exact EMD/Kaluza tests as the geometric setting.  The full local Kaluza
recognition theorem should be presented only as a later corollary if its
realization and constancy seams close.
