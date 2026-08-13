# Analytic realization of the active EMD metric-three-jet collision

Status: proof note for specialist audit, 2026-08-13

## 1. Result

Let `a` be a real constant.  In the conventions of
`docs/EMD_CONVENTION.md`, consider the source-free
Einstein--Maxwell--dilaton equations

```text
Ric_mn = (1/2) exp(a phi)
           (F_mr F_n^r - (1/4) g_mn F_rs F^rs)
         + (1/2) (partial_m phi)(partial_n phi),                 (E)

dF = 0,                                                         (M1)
div_g(exp(a phi) F) = 0,                                       (M2)

box_g phi = (a/4) exp(a phi) F_rs F^rs.                        (S)
```

The purpose of this note is to justify the following upgrade of the finite
jet result in `ThirdOrderMatterJetAmbiguity.lean`.

> **Conditional analytic solution-germ realization theorem.** Assume the EMD
> involutivity lemma stated and argued in Section 3.  Then there are genuine
> local real-analytic EMD solution germs
>
> ```text
> (g_sqrt3, F_sqrt3, phi_sqrt3)  at a = sqrt(3),
> (g_1,     F_1,     phi_1)      at a = 1,
> ```
>
> represented in one fixed coordinate chart about the origin, such that
>
> ```text
> j^3_0 g_sqrt3 = j^3_0 g_1.
> ```
>
> This common metric jet is exactly the explicit normal-coordinate jet
> `g0=minkowskiMetric`, `g1=0`, `activeAmbiguityFormalMetricJet2`,
> `activeAmbiguityFormalMetricJet3`.  Its mixed Ricci endomorphism at the
> origin has the four distinct real eigenvalues
>
> ```text
> -1, 1, (3-sqrt(65))/4, (3+sqrt(65))/4,
> ```
>
> and both matter germs are on the active locus at the origin.  Their
> exponentially rescaled Maxwell first jets are different.  In fact, the
> corresponding unrescaled physical Maxwell first jets are already different.

Since real-analytic fields are smooth, this also gives two genuine smooth
solution germs.  It does **not** give a closed-form exact solution, a common
metric beyond order three, or a global spacetime.

The realization step uses B. Kruglikov, *Involutivity of field equations*,
Journal of Mathematical Physics **51** (2010), 032502,
[arXiv:0902.1685](https://arxiv.org/abs/0902.1685),
[doi:10.1063/1.3305321](https://doi.org/10.1063/1.3305321).  Theorem 3 there
proves involutivity of source-free Einstein--Maxwell in potential variables,
Lemma 4 supplies the determined scalar-wave block, and Theorem 7 gives
analytic realization of compatible prescribed finite jets.  Kruglikov does
not state EMD by name.  Section 3 gives our extension of his symbol and
compatibility argument; it does not invoke Theorem 4 directly and should be
checked independently before submission.

## 2. The finite data in physical variables

### 2.1 Rescaled field

Put

```text
H = exp(a phi/2) F / sqrt(2).
```

This is the curvature-normalized field used by the repository.  The Maxwell
part of the right side of (E) is exactly the ordinary Maxwell stress of `H`.
The Maxwell equations become

```text
dH     =  (a/2) dphi wedge H,                                  (R1)
d(* H) = -(a/2) dphi wedge (* H).                              (R2)
```

At the origin prescribe

```text
g0   = diag(-1,1,1,1),              g1 = 0,
phi0 = 0,                           phi1 = v = (1,0,2,0),
phi2 = 0,
H0   = activeAmbiguityMaxwellField = canonicalMaxwellTwoForm(1,1),
H1   = activeAmbiguityMaxwellFirstJet(a).
```

The companion Hodge jet is
`activeAmbiguityMaxwellHodgeFirstJet(a)`.  The Lean development proves all of
the following finite identities:

1. the point and first-jet Hodge relations;
2. (R1) and (R2) at the origin;
3. the point scalar equation, because `H0_rs H0^rs=0` and `phi2=0`;
4. the point Einstein equation for the fixed `g2`;
5. the first prolongation of the Einstein equation for the fixed `g3`;
6. activity of the physical complexion jet; and
7. simple real spectrum of the common point Ricci endomorphism.

The exact Lean anchors are
`activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling`,
`activeAmbiguityMaxwellFirstJet_injective`,
`activeAmbiguityRicciSource_has_four_distinct_real_eigenpairs`, and
`activeAmbiguity_simpleSpectrum_commonFormalMetricThreeJet_for_every_coupling`.

### 2.2 Unrescaling

Define the physical Maxwell point and first jet by differentiating

```text
F = sqrt(2) exp(-a phi/2) H.
```

Thus

```text
F0_mn       = sqrt(2) H0_mn,
(F1)_r,mn   = sqrt(2) [(H1)_r,mn - (a/2) v_r H0_mn].            (2.1)
```

Exteriorizing (2.1) and using (R1) gives `dF=0`.  Similarly,

```text
exp(a phi) *F = sqrt(2) exp(a phi/2) *H,
```

and (R2) gives (M2).  Hence `(F0,F1)` is an admissible physical Maxwell
one-jet for the coupling `a`.

The two physical first jets are visibly distinct.  With the repository's
component conventions, (2.1) gives

```text
(F1)_0,01 = -sqrt(2) a.
```

It is therefore `-sqrt(6)` at `a=sqrt(3)` and `-sqrt(2)` at `a=1`.

### 2.3 An explicit potential two-jet

The closure identity for `F1` is enough to construct a potential jet; no
Poincare lemma is being assumed at this finite stage.  Set `A_n(0)=0` and

```text
A_n,m       = (1/2) F0_mn,
A_n,mr      = (1/3) [(F1)_r,mn + (F1)_m,rn].                   (2.2)
```

The last expression is symmetric in `m,r`, as a second derivative must be.
Antisymmetry of `F0` gives

```text
A_n,m - A_m,n = F0_mn.
```

For the second identity, use

```text
(F1)_r,mn + (F1)_m,nr + (F1)_n,rm = 0.
```

A direct substitution then gives

```text
A_n,mr - A_m,nr = (F1)_r,mn.
```

Thus (2.2) is a compatible holonomic coefficient two-jet of a one-form
potential with
`j^1(dA)=(F0,F1)`.  It is the quadratic Taylor coefficient obtained from the
radial homotopy formula

```text
A_n(x) = integral_0^1 t x^m F_mn(t x) dt.
```

This explicit construction puts the coefficient data in the potential
variables used by the formal-PDE argument below.  It does not yet exhibit an
actual quadratic one-form field and identify its nested Fréchet derivatives.

The family-specific Lean handoff is now explicit:
`matrixExteriorDerivative_activeAmbiguityPhysicalMaxwellFirstJet` proves
that the correctly unweighted physical first jet is closed for every (a),
and `activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes` instantiates
the radial formula (2.2).  Thus closure is not merely an uninstantiated
hypothesis of the generic potential-jet lemma.

## 3. Why the analytic EMD system is involutive

This section separates the cited result from its application.

### 3.1 What Kruglikov proves

Kruglikov treats a PDE as a submanifold of a jet bundle.  An involutive
system is formally integrable: every compatible finite formal solution lifts
through every higher prolongation.  In the analytic category the
Cartan--Kahler theorem then realizes a compatible finite jet by a local
analytic solution.

The three ingredients used here are precise:

- Theorem 3 proves involutivity of the gauge-degenerate, source-free
  Einstein--Maxwell system in potential variables.
- Lemma 4 supplies the involutive symbol for a determined differential
  operator; it applies to the scalar wave block.
- Theorem 7 records the analytic realization consequence for compatible
  prescribed finite jets of an involutive analytic system.

Theorem 4 is useful context for the role of stress conservation, but it is
not invoked directly below.  Kruglikov does not state EMD by name.

### 3.2 EMD application lemma

> **EMD involutivity lemma.** For every fixed real `a`, write source-free EMD
> in the pure second-order potential variables `(g,A,phi)`, with `F=dA`, on
> the open bundle of nondegenerate metrics.  This analytic system is formally
> integrable.  Its principal-symbol complex is Kruglikov's gauge-degenerate
> Einstein--Maxwell potential complex together with one determined scalar-wave
> block.

Here is the argument.

Use fields `(g,A,phi)`, all governed by second-order equations.  The
highest-order pieces are:

```text
Einstein:  the ordinary second-order Ricci/Einstein symbol in g;
Maxwell:   the gauge-degenerate potential symbol for div_g(exp(a phi) dA);
scalar:    g^{mn} partial_m partial_n phi.
```

The nonzero analytic factor `exp(a phi)` only rescales the Maxwell principal
symbol.  Derivatives of that factor, the dilaton source, and the complete
stress tensor are lower order.  The `(g,A)` principal complex is therefore
the one calculated in Kruglikov's Theorem 3.  Adding `phi` contributes the
determined scalar-wave block covered by Lemma 4.  The direct sum retains the
required Spencer-cohomology vanishings.

It remains to check the coupled compatibility at the first obstruction
order.  Diffeomorphism and Maxwell-gauge invariance of the analytic EMD action
give the off-shell
Noether identity

```text
div_g T_EMD
  = (scalar Euler--Lagrange expression) dphi
    + contraction(F, Maxwell Euler--Lagrange expression),       (3.1)
```

Here `F=dA`, so `dF=0` is automatic.  The Maxwell and scalar equations imply
`div_g T_EMD=0`, which is precisely the differential compatibility needed by
the Einstein block.  The Maxwell gauge identity is already part of the
Theorem-3 potential complex, and the determined scalar wave equation adds no
new compatibility condition.

The symbol and compatibility diagram is therefore the Theorem-3 diagram plus
the determined scalar row, with the lower-order arrows tied together by
(3.1).  The same symbol argument proves the lemma.

This is an **application argument**, not a verbatim theorem from Kruglikov.
It deliberately stays in the unreduced, gauge-degenerate potential system;
no Lorenz-gauge propagation theorem and no direct appeal to Theorem 4 are
being smuggled in.  Before submission, a formal-PDE specialist should audit
the direct-sum symbol claim and the Noether compatibility at the indicated
order.

## 4. Completing and preserving the prescribed third metric jet

The finite repository data specify only the components needed through the
first Einstein prolongation.  The following completion argument is important:
one must not invoke analytic existence on an incomplete jet.

### 4.1 Lift once by formal integrability

For fixed `a`, first lift the closed Maxwell data by (2.2).  The primary PDE
data are then

```text
(g0,g1,g2; A0,A1,A2; phi0,phi1,phi2),
```

satisfying the unprolonged potential EMD equations by Section 2.  Formal
integrability of the EMD system makes the
projection from its first prolongation onto this base equation surjective.
It therefore supplies at least one compatible collection

```text
(g3_tilde, A3, phi3),
```

satisfying all first prolongations.

### 4.2 Why changing only `g3` leaves the matter prolongations unchanged

The first prolongation of (M1)--(M2) differentiates a first-order equation in
`F`.  In normal coordinates it can involve `F2`, `phi2`, and at most `g2`:
one derivative of the connection or Hodge star contains second derivatives
of the metric.  It cannot contain `g3`.

The first prolongation of (S) differentiates

```text
g^{mn}(partial_m partial_n phi - Gamma^r_mn partial_r phi)
  - (a/4) exp(a phi) F^2 = 0.
```

It can involve `phi3`, `F1`, and at most `g2`.  Differentiating `Gamma`
produces `g2`, not `g3`.  It also cannot contain `g3`.

In potential variables the Maxwell equation is second order in `A`; its
first prolongation contains `A3` and at most `g2`, for the same reason.  Thus
the matter prolongations remain true if `g3_tilde` is replaced while all
lower metric jets and matter jets are held fixed.

### 4.3 Replacing `g3_tilde` by the explicit common `g3`

Both the formally supplied `g3_tilde` and
`activeAmbiguityFormalMetricJet3` have the same lower metric jets and matter
jets.  Because the supplied jet lies in the first prolongation, its Ricci
first derivative equals the derivative of the EMD source.

The Lean theorem
`activeAmbiguityFormalMetricJet3_einsteinFirstProlongation`, together with
`activeAmbiguityRicciSourceFirstJet_eq_common`, proves that the explicit
common `g3` has exactly that same Ricci first derivative for every `a`.
Therefore replacing

```text
g3_tilde  by  activeAmbiguityFormalMetricJet3
```

preserves the first Einstein prolongation.  Section 4.2 shows that it also
preserves every first matter prolongation.  We have consequently produced a
**complete compatible EMD formal three-jet whose metric part is the prescribed
common three-jet**.

There is also a direct necessary-compatibility check.  The fully symmetric
metric third jet is proved in Lean to produce the displayed Ricci first jet by
the actual product-rule coordinate Ricci formula.  The normal-coordinate
contracted-Bianchi contraction of that symmetric third jet vanishes by the
usual index symmetries.  This last contraction is part of the human
realization argument; the repository does not formalize the Spencer or
Cartan--Kahler step.

### 4.4 Analytic realization

Apply the standard analytic Cartan--Kähler consequence of involutivity, as
used in Kruglikov's Theorems 6--7, via the EMD involutivity lemma of Section 3,
to the complete compatible three-jet just constructed.  It gives a local
real-analytic EMD solution germ realizing that entire jet.  Perform this
construction separately for `a=sqrt(3)` and `a=1`.  The replacement in
Section 4.3 uses the same fixed `g3` in both cases, hence

```text
j^3_0 g_sqrt3 = j^3_0 g_1.
```

The point spectrum and activity are algebraic first-jet properties already
proved for this common finite data, so they hold for the analytic germs at
the origin.  Their relevant nonvanishing inequalities also persist after
shrinking the neighborhoods, although equality of the two metric jets is
asserted only at the origin.

This proves the theorem stated in Section 1 conditional only on the explicitly
identified EMD involutivity lemma.

## 5. What this changes, and what it does not

If the EMD application lemma passes specialist audit, the earlier phrase
"finite formal-jet ambiguity" is no longer the sharp boundary.  The result is
a solution-level lower bound:

> On an active, simple-real-spectrum point locus, a Lorentzian metric
> three-jet does not identify the constant EMD coupling square.  This remains
> true even when the jet is required to arise from a genuine local analytic
> EMD solution.

The Kaluza value `a^2=3` and the control value `a^2=1` occur over exactly the
same metric three-jet.  The repository's fixed next-order channel returns
their different squares, so the example supplies the intended one-order
separation mechanism.

The result still does not establish any of the following:

- a closed-form previously unknown Kaluza spacetime;
- equality of the two metrics through fourth order or on a neighborhood;
- global existence, completeness, asymptotic conditions, or a black-hole
  interpretation;
- a Lean formalization of Cartan--Kahler, Spencer cohomology, Kruglikov's
  theorem, or the EMD application lemma; or
- priority or novelty relative to every unpublished or differently phrased
  result in the EMD/Rainich literature.

For publication, the potential-system EMD involutivity lemma is the single point
that most deserves an independent expert check.  Everything downstream of it
is an explicit jet-completion and replacement argument, and its finite
algebraic identities are either elementary formulas above or compiled Lean
theorems in the repository.
