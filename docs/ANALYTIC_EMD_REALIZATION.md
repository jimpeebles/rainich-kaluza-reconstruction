# Analytic realization of the active EMD metric-three-jet continuum

Status: proposition-level proof note for specialist audit, 2026-08-13

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

> **Analytic solution-germ realization theorem (external-theorem
> dependent).** Assuming Kruglikov's published Einstein--Maxwell Spencer
> calculation and the standard analytic Cartan--Kahler realization theorem,
> for every real `a` there is a genuine local real-analytic EMD solution germ
>
> ```text
> (g_a, F_a, phi_a)  at coupling a,
> ```
>
> represented in the fixed coordinate chart about the origin, such that
>
> ```text
> j^3_0 g_a = J_common
> ```
>
> for the same `J_common`, independently of `a`.  Hence every nonnegative
> coupling square occurs over this one metric three-jet.  In particular,
>
> ```text
> j^3_0 g_sqrt3 = j^3_0 g_1,
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
> and every matter germ is on the active locus at the origin.  The
> corresponding unrescaled physical Maxwell first jet is an injective function
> of `a`, even though the metric three-jet is constant.

Since real-analytic fields are smooth, this also gives a smooth solution germ
for every real coupling.  It does **not** give a closed-form exact solution, a
common metric beyond order three, or a global spacetime.  The construction is
performed separately for each fixed `a`; no common neighborhood or analytic
dependence of the solution germ on the parameter `a` is asserted.

The realization step uses B. Kruglikov, *Involutivity of field equations*,
Journal of Mathematical Physics **51** (2010), 032502,
[arXiv:0902.1685](https://arxiv.org/abs/0902.1685),
[doi:10.1063/1.3305321](https://doi.org/10.1063/1.3305321).  Theorem 3 there
proves involutivity of source-free Einstein--Maxwell in potential variables:
on pp. 6--8 Kruglikov explicitly introduces `A`, sets `F=dA`, labels the
pure second-order system as equation (10), and gives
`H^(0,0)=S^2 T* ⊕ T*`.  His following Remark 3 separately records the
mixed-order two-form formulation, whose `H^(0,0)` contains `Λ^2 T*`.
Thus the potential formulation used below is the cited one, not an inference
from that mixed-order remark.  Lemma 4 supplies the determined scalar-wave
block.  His general formal
theory discussion and Theorems 5--7 record the prescribed-finite-jet
Cartan--Kahler consequence in the systems treated there.  Theorem 7 itself is
specific to the class in his Theorem 4, so it is **not** cited as a verbatim
EMD theorem here.  Kruglikov does not state EMD by name.  Section 3 gives the
missing pure-order-two EMD symbol and compatibility proof explicitly.  It is
a short consequence of his computed complexes, rather than an additional
unexpanded involutivity assumption, but it should still receive specialist
audit before submission.

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
`activeAmbiguityPhysicalMaxwellFirstJet_injective`,
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
variables used by the formal-PDE argument below.  The Lean theorem
`activeAmbiguityPhysicalRadialPotentialPolynomial_realizes` now exhibits the
actual quadratic one-form field and identifies its first and second nested
Fréchet derivatives; its curl theorem recovers the physical Maxwell value and
first jet.

The family-specific Lean handoff is now explicit:
`matrixExteriorDerivative_activeAmbiguityPhysicalMaxwellFirstJet` proves
that the correctly unweighted physical first jet is closed for every (a),
and `activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes` instantiates
the radial formula (2.2).  Thus closure is not merely an uninstantiated
hypothesis of the generic potential-jet lemma.

## 3. Involutivity of the analytic EMD potential system

This section gives a proposition-level reduction to a published Spencer
calculation.  Labels below distinguish an explicit calculation made here
from an external theorem.

### 3.1 The exact pure-order-two PDE map (direct calculation)

Let `M` be four-dimensional and fix `a in R`.  On the open bundle

```text
E_nd = S^2_nd(T* M)  +  T* M  +  R
```

of nondegenerate metrics, one-form potentials, and scalars, put
`F=dA`, `v=dphi`, `f=exp(a phi)`, and define

```text
S_a[g,A,phi] = integral sqrt(|det g|)
  [R - (1/4) f F^2 - (1/2) v^2] d^4x.
```

In the repository normalization, define

```text
P_a : J^2(E_nd) -> S^2(T* M) + T* M + R
```

by the following equivalent repository-normalized expressions

```text
(E_g)_mn = Ric_mn
  - (1/2) f (F_mr F_n^r - (1/4) g_mn F^2)
  - (1/2) v_m v_n,

(E_A)_n = nabla^m (f F_mn),

E_phi = box_g phi - (a/4) f F^2.                         (3.1)
```

Thus source-free EMD is `P_a=0`.  The displayed `E_g` is the
trace-reversed metric Euler--Lagrange equation.  If instead

```text
Ehat_g = G - (1/2) T_Maxwell - (1/2) T_scalar,
```

then, in four dimensions,

```text
E_g = Ehat_g - (1/2) tr_g(Ehat_g) g,
Ehat_g = E_g - (1/2) tr_g(E_g) g.                         (3.1a)
```

The trace-reversal map is an involution, so both systems have identical zero
sets and isomorphic metric equation symbols.  This is why the symbol below is
written using the Ricci symbol, exactly as in the finite Lean data.  The PDE
map is real analytic on every
fixed-signature component: inverse metric entries are rational functions with
nonzero determinant denominator, and the only non-polynomial coefficient is
the analytic function `exp(a phi)`.

This formulation is important.  All unknowns occur in equations of order
two, `dF=0` is the identity `d^2 A=0`, and no gauge choice has been imposed.

### 3.2 The principal symbol is an exact block sum (direct calculation)

Order the unknowns as `(g,A,phi)` and the equations as
`(E_g,E_A,E_phi)`.  Inspection of (3.1) gives

```text
sigma_2(P_a) = diag(
  sigma_2(Ric),
  f sigma_2(delta_g d),
  tr_g).                                                   (3.2)
```

There are no omitted off-diagonal second-order entries:

- the EMD stress in `E_g` contains only first derivatives of `A` and `phi`;
- `E_A` contains second derivatives of `A`, but only first derivatives of
  `g` and `phi`; and
- `E_phi` contains second derivatives of `phi`, but only first derivatives
  of `g` and `A`.

Since `f=exp(a phi)>0`, its factor does not change the Maxwell symbol kernel.
Consequently the full symbolic system, including every formal prolongation,
is the direct sum of the vacuum-Einstein symbol, Kruglikov's Maxwell-potential
symbol, and the scalar-wave symbol.  Notice that the exponential gauge
coupling is lower order in the formal-PDE sense; this is not the
curvature-coupled scalar system discussed as a more delicate example at the
end of Kruglikov's paper.

The three diagonal symbols are epimorphic at order two for every
nondegenerate `g`.  Hence `P_a=0` is locally a smooth codimension-15
submanifold of `J^2(E_nd)`, and its projection to `J^1(E_nd)` is a
submersion.  No non-null, activity, or simple-spectrum assumption is needed
for this PDE regularity.  In particular, the fact that the witness has
`F^2=0` causes no symbol-rank loss.

For an explicit resolution, set

```text
V = S^2 T* + T* + R        (unknowns),
W = S^2 T* + T* + R        (equations),
C = T* + R                 (compatibilities).
```

For every `r >= 1`, the direct sum of Kruglikov's Einstein and Maxwell
resolutions with the determined scalar row is the exact symbol sequence

```text
0 -> g_(r+2)
  -> S^(r+2) T* tensor V
  -> S^r T* tensor W
  -> S^(r-1) T* tensor C
  -> 0.                                                    (3.2a)
```

The final symbol sends a decomposable first equation derivative to

```text
p tensor (h, alpha, s)
  |-> (sigma_divG(p tensor h), <p,alpha>_g),

sigma_divG(p tensor h)_n
  = p^m h_mn - (1/2) p_n tr_g(h);
```

it ignores the scalar-equation slot `s`.  These two entries are the
contracted-Bianchi and Maxwell-divergence symbols.  At `r=0`, the sequence
ends at `W`, because the order-two equation symbol is epimorphic.  The
nonlinear lower-order completion of this final symbol is given explicitly in
(3.6)--(3.8).

### 3.3 Spencer cohomology, characters, and rank predictions

**External input.**  Kruglikov's Theorem 3 computes for the pure-order-two
Einstein--Maxwell potential system

```text
H^(0,0) = S^2 T* + T*,
H^(1,1) = S^2 T* + T*,
H^(1,2) = T* + R,
```

with all other Spencer groups zero, and proves involutivity.  His Lemma 4
gives for one determined second-order scalar equation

```text
H^(0,0) = R,    H^(1,1) = R,
```

with all other groups zero.

**Consequence of the direct sum (3.2).**  The only nonzero cohomology of the
EMD symbol is therefore

```text
H^(0,0)(EMD) = S^2 T* + T* + R,
H^(1,1)(EMD) = S^2 T* + T* + R,
H^(1,2)(EMD) = T* + R.                                  (3.3)
```

In four dimensions, Kruglikov's character formula gives the following exact
check:

```text
                         s1  s2  s3  s4
vacuum Einstein          40  30  16   4
Maxwell potential        16  12   7   1
scalar wave               4   3   2   0
------------------------------------------------
EMD total                60  45  25   5.                 (3.4)
```

Thus

```text
dim g_2(EMD) = 60+45+25+5 = 135,
dim g_3(EMD) = 60+2*45+3*25+4*5 = 245.                  (3.5)
```

The first number also follows from `150-15`: there are 150 pure second
derivative coefficients and 15 independent equations.  At order three there
are 300 pure third derivative coefficients and 60 differentiated equations,
but the five compatibility symbols in `T*+R` leave rank 55, hence
`300-55=245`.  Equations (3.4)--(3.5) are exact predictions for an independent
symbol-rank computation at the witness, not numerical assumptions.

That independent computation now exists in
`validation/benchmarks/vt3_emd_symbol_involutivity.py`.  Over exact rational
arithmetic it verifies:

```text
rank sigma_2 = 15,       dim g_2 = 135,
rank sigma_3 = 55,       dim g_3 = 245,
characters = (60,45,25,5),
dim g_4 = 395,           dim g_5 = 590.
```

It also reconstructs the 15-by-150 symbol independently by differentiating
the full coordinate EMD residual evaluator at the active lower jet, and proves
that the `T*+R` syzygy rows exhaust the exact left kernels through three
prolongations.  The evaluator uses the trace-reversed Ricci equation, which
is related to the Einstein-tensor equation by the invertible map (3.1a).
Thus the rank-15 computation also verifies submersion in the highest-jet
directions at the actual witness.  This is a falsification certificate, not a
replacement for the published all-order Spencer theorem or for the
lower-order Noether calculation.

### 3.4 The five compatibility components vanish (direct calculation)

It remains to evaluate the structure obstruction in (3.3).  There are only
five possible components: four from contracted Bianchi and one from Maxwell
gauge invariance.

First, for every two-form `K`, `delta_g^2 K=0`.  Taking `K=fF` gives the
off-shell identity

```text
nabla^n (E_A)_n = 0.                                      (3.6)
```

In coordinates it is also immediate by commuting the two covariant
derivatives of the antisymmetric tensor `f F^{mn}`; the two Ricci contractions
cancel.  This is the scalar compatibility generator in Kruglikov's Maxwell
complex.

For the four Bianchi components, the two elementary divergence calculations
are

```text
nabla^m [f(F_mr F_n^r - (1/4)g_mn F^2)]
  = F_n^r (E_A)_r - (a/4) f F^2 v_n,

nabla^m [v_m v_n - (1/2)g_mn v^2]
  = (box_g phi) v_n.                                     (3.7)
```

The first uses only `dF=0`, which is an identity because `F=dA`; the second
uses commutation of covariant derivatives on a scalar.  With the one-half
normalizations in (3.1), (3.7) combines to the exact off-shell Noether
identity

```text
nabla^m [(E_g)_mn - (1/2) tr_g(E_g) g_mn]
  = -(1/2) F_n^r (E_A)_r - (1/2) v_n E_phi.              (3.8)
```

Thus both components of `H^(1,2)=T*+R` vanish modulo `P_a=0`.  Their leading
symbols are respectively the Bianchi and Hodge compatibility symbols used in
Kruglikov's Theorem 3, so (3.6)--(3.8) account for the entire obstruction
space, rather than merely exhibiting some relations among the equations.

### 3.5 EMD involutivity proposition

> **Proposition.** For every fixed real `a`, the analytic, gauge-degenerate,
> pure-order-two EMD potential system (3.1) is involutive on the bundle of
> nondegenerate metrics.  Its Spencer cohomology is (3.3), its four-dimensional
> Cartan characters are (3.4), and it is formally integrable.

**Proof.**  Equation (3.2) and Kruglikov's Theorem 3 and Lemma 4 show that the
symbol is involutive and give (3.3).  For a pure-order-two system with this
regular symbol, Kruglikov's Section 1 states that formal-integrability
obstructions are Spencer classes and that an involutive symbolic system
requires checking only the first structure class.  Here that class lies in
`H^(1,2)=T*+R`; identities (3.6)--(3.8) annihilate all its components.  Thus
the symbol and structure tensor are involutive in precisely his definition,
and formal integrability follows.  The character and dimension claims follow
from his Proposition 2 and the direct sums above.  QED.

> **Robustness corollary.**  The same proof, cohomology, and Cartan characters
> apply to the four-dimensional action
>
> ```text
> integral sqrt(|det g|)
>   [R - (1/4) f(phi) F^2 - (1/2)(dphi)^2 - V(phi)] d^4x
> ```
>
> on every region where the gauge-kinetic function `f` is real analytic and
> nonzero and the potential `V` is real analytic.  Indeed, the Maxwell symbol
> is merely multiplied by `f`; `f'` and `V'` occur below principal order; and
> the Einstein-tensor residual adds `+(1/2)V(phi)g_mn`, while its
> trace-reversed Ricci residual adds `-(1/2)V(phi)g_mn`.  The corresponding
> diffeomorphism Noether identity
> replaces `E_phi` in (3.8) by
>
> ```text
> box_g phi - V'(phi) - (1/4) f'(phi) F^2.
> ```
>
> EMD is the specialization `f(phi)=exp(a phi)`, `V=0`.  This corollary is a
> consequence of the displayed argument, not a claim of literature priority.

This proof deliberately remains in the unreduced potential system.  It needs
neither Lorenz gauge nor a gauge-propagation theorem.  It also does not invoke
Kruglikov's Theorem 4: his own discussion notes that the Maxwell matter
operator has a differential identity, so treating it as the underdetermined
operator in that theorem would be unjustified.

### 3.6 Dependency ledger

- **Lean-checked repository input:** the finite Einstein, scalar, Maxwell,
  Hodge, activity, and spectrum identities listed in Section 2.
- **Direct human calculation in this note:** the PDE map (3.1), block symbol
  (3.2), character arithmetic (3.4)--(3.5), and identities (3.6)--(3.8).
- **Exact independent regression:**
  `validation/benchmarks/vt3_emd_symbol_involutivity.py` and its committed
  artifact reconstruct ranks, characters, finite prolongations, syzygy
  exhaustion, and the full-coordinate active-witness symbol without floating
  point arithmetic.  Its evidence class is deliberately
  `exact-rational-symbol-certificate-not-formal-integrability-proof`.
- **Published external input:** Kruglikov Theorem 3 and Lemma 4, plus the
  Cartan--Kahler theorem for a regular analytic involutive system as developed
  in R. Bryant, S.-S. Chern, R. Gardner, H. Goldschmidt, and P. Griffiths,
  *Exterior Differential Systems*, MSRI Publications 18, Springer (1991),
  [doi:10.1007/978-1-4613-9714-4](https://doi.org/10.1007/978-1-4613-9714-4).
  Kruglikov's Theorems 5--7 give the prescribed-jet form for his field-equation
  examples.
- **Not independently formalized here:** Kruglikov's all-order Spencer diagram
  chase, the general theorem identifying and killing the structure class, and
  Cartan--Kahler itself.  The coordinate sign/factor calculations in
  (3.1a) and (3.6)--(3.8) are transparent but human.  A specialist audit
  remains desirable because the EMD proposition is a new application, not a
  theorem stated verbatim in the cited paper.

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

satisfying the unprolonged potential EMD equations by Section 2.  The
proposition in Section 3 makes the projection from the first prolongation
onto this base equation surjective.  It therefore supplies at least one
compatible collection

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
the actual Fréchet derivative of the composed coordinate Ricci field:
`activeAmbiguityPolynomialMetricGerm_actualRicci_coordinateFDeriv_zero`
uses the compiled matrix-inverse chain rule rather than an independently
supplied inverse-metric derivative.  The normal-coordinate
contracted-Bianchi contraction of that symmetric third jet vanishes by the
usual index symmetries.  This last contraction is part of the human
realization argument; the repository does not formalize the Spencer or
Cartan--Kahler step.

### 4.4 Analytic realization

Apply the standard analytic Cartan--Kähler consequence for a regular analytic
involutive system to the complete compatible three-jet just constructed.  It
gives a local real-analytic EMD solution germ realizing that entire jet.
Kruglikov's Theorem 6 is the exact Einstein--Maxwell analogue of this use;
his Theorems 5--7 illustrate the same prescribed-jet consequence for the
systems treated there, but Theorem 7 is not being applied directly to EMD.
Perform this construction for an arbitrary fixed `a`.  The replacement in
Section 4.3 uses the same fixed `g3` for every value of `a`, hence

```text
for every a in R,  j^3_0 g_a = J_common.
```

In particular,

```text
j^3_0 g_sqrt3 = j^3_0 g_1.
```

The point spectrum and activity are algebraic first-jet properties already
proved for this common finite data, so they hold for the analytic germs at
the origin.  Their relevant nonvanishing inequalities also persist after
shrinking the neighborhoods, although equality of the two metric jets is
asserted only at the origin.

This proves the theorem stated in Section 1 from the Section-3 proposition and
the published external results itemized in Section 3.6.

## 5. What this changes, and what it does not

The proposition-level proof above upgrades the earlier phrase "finite
formal-jet ambiguity" to a solution-level lower bound, conditional only in
the ordinary mathematical sense on the cited Spencer and Cartan--Kähler
theorems.  Because the EMD extension is not stated verbatim in the reference,
the upgrade should remain marked "pending specialist audit" in outward-facing
claims until that audit occurs:

> On an active, simple-real-spectrum point locus, a Lorentzian metric
> three-jet does not identify the constant EMD coupling square.  This remains
> true even when the jet is required to arise from a genuine local analytic
> EMD solution.

Indeed, if a metric-only rule `I` of differential order at most three returned
`a^2` on every such solution germ, then `I` would factor through the metric
three-jet.  Evaluating it on the common jet at `a=1` and `a=sqrt(3)` would give
simultaneously

```text
I(J_common) = 1    and    I(J_common) = 3,
```

a contradiction.  This is a solution-space lower bound, not merely a failure
of one proposed reconstruction algorithm.

More strongly, every nonnegative value of `a^2` occurs over exactly the same
metric three-jet: for `c >= 0`, choose `a=sqrt(c)`.  The Kaluza value `3` and
the control value `1` are two distinguished members of this continuum.  The
repository's fixed next-order channel returns the corresponding square for
each member, so the example supplies the intended one-order separation
mechanism.

The result still does not establish any of the following:

- a closed-form previously unknown Kaluza spacetime;
- equality of the two metrics through fourth order or on a neighborhood;
- global existence, completeness, asymptotic conditions, or a black-hole
  interpretation;
- a Lean formalization of Cartan--Kahler, Spencer cohomology, Kruglikov's
  theorem, or the EMD application lemma; or
- priority or novelty relative to every unpublished or differently phrased
  result in the EMD/Rainich literature.

For publication, the block-symbol and obstruction argument in Section 3 is
the single point that most deserves an independent expert check.  The note now
exposes every component needed for that check: the PDE map, all symbol blocks,
Spencer groups, Cartan characters, rank predictions, and both off-shell
identities.  Everything downstream is an explicit jet-completion and
replacement argument, and its finite algebraic identities are either
elementary formulas above or compiled Lean theorems in the repository.
