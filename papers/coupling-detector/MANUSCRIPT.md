# Third-order non-identifiability and fourth-order physical-channel recovery of the Einstein--Maxwell--dilaton coupling square from metric jets

## Abstract

We ask whether the constant coupling magnitude \(a^2\) in four-dimensional
Einstein--Maxwell--dilaton (EMD) theory can be inferred from the metric alone.
The answer has a sharp jet-order structure on an explicit active, non-null,
simple-spectrum branch.

First, modulo one explicit analytic EMD involutivity lemma for which we give a
direct symbol/Noether argument pending specialist audit, we construct a
one-parameter family of local analytic EMD solution germs, indexed by the real
coupling \(a\), whose metric three-jets at a common
normal-coordinate point are identical.  Their matter first jets are distinct
and injectively record \(a\); their common mixed Ricci tensor has four distinct
real eigenvalues; and the physical Maxwell-complexion activity condition is
nonzero.  Thus even on this nondegenerate solution locus, no construction from
the metric three-jet can identify \(a^2\).

Second, relative to the curvature-normalized Maxwell seed, the complete first
differentiated exterior channels determine

\[
  A=a\cos(2\theta),\qquad
  \eta=d\theta+\frac{B}{2}Jv,
  \qquad B=a\sin(2\theta),
\]

where \(v=d\phi\) and \(J\) is the normalized Maxwell-stress involution.  The
channels have fibers that, when the seed amplitude and scalar covector are
nonzero, are exactly the free affine shear orbits

\[
  B\mapsto B+\tau,\qquad
  d\theta\mapsto d\theta-\frac{\tau}{2}Jv.
\]

Equality of the complete channels is equivalent to equality of \(A\) and
membership of \((d\theta,B)\) in one unique such orbit.  Thus the third-order
ambiguity is precisely \(\mathbb R\), rather than merely an exhibited
one-parameter family.

Constancy of \(a\) supplies one derivative later

\[
  dA+2B\eta-B^2Jv=0.
\]

On the active locus \(\eta\wedge Jv\ne0\), this gives a component-independent
quotient for \(B\), and hence \(a^2=A^2+B^2\).  On the explicit active formal
family, the fixed fourth-order outputs for \(a\) and \(b\) agree if and only if
\(a=\pm b\): the order-three \(\mathbb R\)-fiber collapses at order four to the
orientation-free \(\mathbb Z_2\).  We also implement a finite
coordinate detector whose nested Fréchet-derivative definitions reach metric
order four by dependency tracing.  We have not yet compiled a separate
factorization through a packaged coordinate four-jet.  Under its
explicit active-regular Ricci--exterior EMD hypotheses, its accepted set is
nonempty and contains the physical value \(a^2\); with a certificate for every
survivor on the unique scalar-closure locus, the complete output image is
\(\{a^2\}\).  Kaluza reduction gives the necessary selector \(a^2=3\).

The finite collision jet, channel obstruction and recovery, detector
construction, and correctness implications are checked in Lean.  The
upgrade from compatible finite jets to analytic solution germs uses
Cartan--Kähler theory and a short symbol extension of Kruglikov's involutivity
theorem for source-free Einstein--Maxwell equations; that formal-PDE step is a
human mathematical argument pending specialist audit, not part of the Lean
proof.  We do not claim full nonlinear-coordinate covariance for the finite
detector, a metric-only converse, or a new closed-form spacetime.

## 1. Problem and result hierarchy

Use signature \((-+++)\) and the action

\[
  \mathcal L=\sqrt{-g}\left(
    R-\frac14e^{a\phi}F_{\mu\nu}F^{\mu\nu}
      -\frac12\nabla_\mu\phi\nabla^\mu\phi\right).
\]

Five-dimensional vacuum Kaluza reduction selects \(a^2=3\).  Classical
Rainich theory asks whether matter fields can instead be reconstructed from
curvature.  Here the inverse problem is harder: the Ricci tensor mixes a
rank-one scalar term with a non-null Maxwell stress, and the coupling enters
only after differentiation.

The paper has four logically distinct results.

1. The complete first curvature-seed channel fibers are exactly the unique
   affine real-shear orbits under the stated nonvanishing hypotheses.
2. Conditional on the explicit EMD involutivity lemma, the kernel is realized
   by active, simple-spectrum analytic EMD solution germs with one common
   metric three-jet for every real coupling.
3. One additional derivative breaks the continuous kernel and recovers
   \(a^2\) in the physical channel; on the explicit active formal family its
   equality fibers are exactly \(a=\pm b\).
4. A finite metric-only coordinate detector realizes the recovery as a
   necessity/correctness theorem under explicit entrance and survivor
   certificates.

Conditional on the stated involutivity lemma, Result 2 is the solution-level
lower bound.  Result 3 is the matching
one-order-higher recovery in the selected physical curvature channel.  Result
4 is deliberately stated with more hypotheses: this paper does not assert
that every analytic germ supplied by Result 2 has already been routed through
every finite detector gate.

## 2. Curvature decomposition and finite branches

Set

\[
  v=d\phi,\qquad H=\frac{e^{a\phi/2}}{\sqrt2}F.
\]

Raising one Ricci index gives

\[
  \mathcal R=S+V,\qquad
  V=\frac12v^\sharp\otimes v,
  \qquad S=\operatorname{MaxwellStress}(H).
\]

On the non-null Maxwell branch,

\[
  S^2=q^2I,\qquad q>0,
\]

while \(V^2=\operatorname{tr}(V)V\).  Eliminating \(S\) yields the
noncommutative reconstruction equation

\[
  \mathcal RV+V\mathcal R-\operatorname{tr}(V)V
    =\mathcal R^2-q^2I.                                      \tag{2.1}
\]

On the labeled real simple-spectrum branch, polynomial projectors reduce
(2.1) to two complementary scalar eigendirections.  Their amplitudes are
fixed, but their relative sign is not.  The metric therefore constructs a
finite zero/one/two list of scalar covectors after exterior closure is tested.
The two pointwise candidates are exchanged by a Ricci-centralizing spectral
reflection.  This algebraic ambiguity is supporting geometry, not the main
jet-order obstruction below.

For a selected scalar branch define \(J=S/q\).  Its negative and positive
planes carry an adapted Maxwell seed pair \((H_0,*H_0)\).  A physical form in
the same stress fibre has

\[
  H=cH_0+s(*H_0),\qquad c^2+s^2=1.
\]

No angle is required globally.  The double-angle scalars

\[
  C=c^2-s^2,\qquad S_2=2cs
\]

and the complexion covector

\[
  \omega=\frac{C\,dS_2-S_2\,dC}{2}=c\,ds-s\,dc             \tag{2.2}
\]

are defined directly from the physical pair.  The construction is invariant
under simultaneous sign reversal and under changes of adapted frame.

## 3. The complete first-channel shear kernel

Write locally \(c=\cos\theta\), \(s=\sin\theta\), and put

\[
  A=a\cos(2\theta),\qquad B=a\sin(2\theta),\qquad
  \eta=d\theta+\frac B2Jv.                                  \tag{3.1}
\]

Rotating the two EMD exterior equations back to the curvature seed gives

\[
\begin{aligned}
  dH_0&=\frac A2v\wedge H_0-\eta\wedge(*H_0),\\
  d(*H_0)&=\eta\wedge H_0-\frac A2v\wedge(*H_0).
\end{aligned}                                                \tag{3.2}
\]

For nonzero canonical seed amplitude and \(v\ne0\), the complete pair of
three-forms in (3.2) determines \((\eta,A)\) uniquely.  It does not determine
\((d\theta,B)\).  For every \(\tau\in\mathbb R\),

\[
  B\longmapsto B+\tau,
  \qquad d\theta\longmapsto d\theta-\frac\tau2Jv             \tag{3.3}
\]

leaves both complete three-forms unchanged.  This is not a bad-probe effect:
the entire channel tensors coincide.  Conversely, any two inputs producing
the same complete tensors have the same \(A\), and their
\((d\theta,B)\) pairs are related by exactly one transformation (3.3).  The
parameter is unique because it is already the difference of the \(B\)
components.

### Theorem I (complete-channel obstruction)

*Claim ledger: C1.*

When the canonical seed amplitude and \(v\) are nonzero, two complete
first-channel inputs agree if and only if their \(A\) components agree and
their \((d\theta,B)\) pairs lie in one affine shear orbit (3.3).  The shear
action is free, so every fiber is one uniquely parameterized copy of
\(\mathbb R\).  Consequently that channel system does not identify
\(a^2=A^2+B^2\).

The theorem is machine checked by
`canonicalFullComplexionCouplingChannels_eq_iff_shearOrbit` and
`canonicalFirstOrderChannelShear_parameter_unique`; the earlier invariance and
noninjectivity theorems are immediate weaker faces of the classification.  By
itself this is a statement about the complete first differentiated seed
channels.  The next section upgrades the lower bound to actual analytic
solutions and therefore excludes every rule based on the common metric
three-jet, not merely rules built from (3.2).

## 4. Active finite collision and the analytic solution-germ upgrade

At a normal-coordinate point use

\[
  g_0=\operatorname{diag}(-1,1,1,1),\qquad g_1=0,
  \qquad v=e^0+2e^2,qquad \nabla^2\phi=0,
\]

and the balanced non-null Maxwell/Hodge pair with electric and magnetic
amplitudes \((1,1)\) and \((-1,1)\).  Add the common first-jet perturbation

\[
  C_{0,12}=2,\qquad C_{2,01}=-2,
\]

and a coupling-dependent infinitesimal duality tangent.  For every \(a\), the
resulting matter jet satisfies both exterior EMD equations.  Its physical
complexion is

\[
  \omega_a=\frac a2e^0+(1-a)e^2,
  \qquad (\omega_a\wedge Jv)_{02}=1,                       \tag{4.1}
\]

so the family is active uniformly in \(a\).

The coupling-dependent tangent lies in the Maxwell-stress kernel.  Hence all
couplings have the same point Ricci source and first Ricci-source jet.  An
explicit symmetric metric second jet and fully symmetric metric third jet
realize those sources.  The common mixed Ricci source is

\[
 \begin{pmatrix}
 -3/2&0&-1&0\\
 0&-1&0&0\\
 1&0&3&0\\
 0&0&0&1
 \end{pmatrix},
\]

with four distinct real eigenvalues

\[
  -1,\quad 1,\quad \frac{3-\sqrt{65}}4,\quad
  \frac{3+\sqrt{65}}4.                                    \tag{4.2}
\]

The finite jet obeys the point Einstein and scalar equations, the first
Einstein/Ricci prolongation, both exterior equations, point/first-jet Hodge
compatibility, and the contracted-Bianchi compatibility condition.  The
Maxwell first jet depends injectively on \(a\).

### Analytic realization lemma

The analytic EMD equations are put in the pure second-order potential
variables \((g,A,\phi)\), with \(F=dA\).  Before invoking any formal-PDE
result, the closed finite Maxwell data above are lifted by an explicit radial
homotopy formula to a potential two-jet \(j^2A\).  The prescribed data are
therefore compatible holonomic coefficient jets in the variables used by the
PDE, not a mixed-order \((g,F,\phi)\) surrogate.  Lean does not yet package
these coefficients as an explicit quadratic one-form field with nested
Fréchet derivatives.

Kruglikov proves involutivity of the gauge-degenerate source-free
Einstein--Maxwell potential system
([Theorem 3](https://arxiv.org/abs/0902.1685)).  The dilaton adds one
determined scalar-wave block, whose symbol has the required involutivity by
his Lemma 4.  The exponential factors and the EMD couplings among \(A\),
\(\phi\), and the stress tensor are lower order, so they do not alter the
combined principal-symbol complex.  The EMD Noether identity makes stress
conservation a differential consequence of the Maxwell and scalar equations,
supplying the contracted-Bianchi compatibility for the Einstein block.  The
Theorem-3 symbol argument therefore extends to analytic EMD, and
Cartan--Kähler realizes compatible finite jets as local analytic solution
germs.

For the displayed family the finite Einstein, Maxwell, scalar, Hodge, and
first-prolongation identities hold, and the contracted-Bianchi residual
vanishes.  The remaining higher matter slots can consequently be completed
without changing the prescribed metric three-jet.  Conditional on the EMD
involutivity lemma, this yields a local analytic EMD germ for every \(a\).

This is a short application argument pending specialist audit, not a quotation
of a theorem in which
Kruglikov names EMD.  In particular, we do not invoke his Theorem 4 directly.
The finite-jet identities, explicit potential coefficient two-jet, and symmetric
metric/Ricci first prolongation are checked in Lean.  The contracted-Bianchi
contraction, Spencer-complex extension, and Cartan--Kähler application belong
to the human proof and are not formalized in Lean.
The complete proof boundary is recorded in
[`docs/ANALYTIC_EMD_REALIZATION.md`](../../docs/ANALYTIC_EMD_REALIZATION.md).

### Theorem II (conditional solution-level non-identifiability of \(a^2\))

*Claim ledger: finite inputs C2--C4; conditional solution upgrade C5--C6.*

Assume the analytic potential-EMD involutivity lemma stated above.  For every
real \(a\), there is a local analytic EMD solution germ
\((g_a,\phi_a,F_a)\) at the displayed point such that:

- all metric three-jets \(j^3g_a\) are equal;
- the matter first jet is injective in \(a\);
- the common mixed Ricci tensor has the four distinct real roots (4.2); and
- the activity component (4.1) is nonzero.

Therefore, for any \(a,b\) with \(a^2\ne b^2\), no function of the metric
three-jet can return the squared coupling on both germs.  In particular,
\(a=\sqrt3\) and \(a=1\) give a Kaluza/non-Kaluza collision with coupling
squares \(3\) and \(1\).

Equality in one fixed normal-coordinate jet is already enough for this
impossibility statement: a covariant metric-three-jet rule is a special case
of a rule on those data.  We do not claim that the two solutions share their
metric four-jets, or that one closed-form expression describes the germs.

## 5. One derivative later: recovery of the coupling square

Because \(a\) is constant,

\[
  dA=-2B\,d\theta.
\]

Eliminating \(d\theta\) with (3.1) gives

\[
  dA+2B\eta-B^2Jv=0.                                    \tag{5.1}
\]

Wedging with \(Jv\) removes the quadratic term.  If

\[
  \Delta_{ij}=(\eta\wedge Jv)_{ij}\ne0,
\]

then

\[
  B=-\frac{(dA\wedge Jv)_{ij}}{2\Delta_{ij}},
  \qquad a_{\rm geom}^2=A^2+B^2.                         \tag{5.2}
\]

All unused components of (5.1) remain compatibility obstructions.  Any two
accepted nonzero components give the same \(B\).  Moreover,

\[
  \eta\wedge Jv=d\theta\wedge Jv,                        \tag{5.3}
\]

so the active locus is independent of the hidden \(B\) and of the coupling.

### Theorem III (fourth-order physical-channel recovery)

*Claim ledger: C7.*

On a genuine constant-coupling EMD solution in the non-null active channel,
the quotient (5.2) is component independent and returns the physical \(B\);
the resulting scalar satisfies

\[
  a_{\rm geom}^2=a^2.
\]

Ricci and the curvature-normalized seed use \(j^2g\), their first channels use
\(j^3g\), and \(dA\) uses \(j^4g\).  Combined with Theorem II, this is a sharp
third-versus-fourth-order separation for coupling-square identifiability on
the displayed active solution class.  It is not yet a claim that the complete
finite accepted-set construction is a diffeomorphism-invariant function of an
abstract four-jet.

There is also a sharp finite-jet statement on the explicit active ambiguity
family of Section 4.  For any real \(a,b\), its fixed fourth-order
coupling-square candidates agree if and only if

\[
  a=b\quad\text{or}\quad a=-b.                            \tag{5.4}
\]

This is machine checked by
`activeAmbiguityFourthOrderCouplingSqCandidates_eq_iff`.  Together with
Theorem I, it gives the exact transition

\[
  \mathbb R\text{-shear fiber at order three}
  \quad\longrightarrow\quad
  \mathbb Z_2\text{ sign fiber at order four}.             \tag{5.5}
\]

The surviving sign is fundamental for a squared-coupling detector: reversing
the scalar orientation changes the oriented coupling presentation while
leaving \(a^2\) unchanged.  Equation (5.4) is a Lean theorem for the explicit
formal family.  The broader scalar-orientation interpretation is a
mathematical observation used throughout the paper, not a newly packaged
all-order Lean symmetry theorem.

## 6. Finite metric-only detector

For a coordinate metric \(g\) and point \(z\), let

\[
  \mathscr D_4(g,z)
\]

be `acceptedActualMetricFourthOrderDetectorChoicesAt g z`.  It is a finite set
formed by enumerating scalar probes, the relative scalar sign, Maxwell
principal-frame probes, one of six Lorentzian pivot recipes, orientation, and
source/wedge components, then filtering them by explicit equalities and strict
inequalities.  For \(\chi\in\mathscr D_4(g,z)\), write

\[
  \widehat a^2(g,z;\chi)
\]

for `actualMetricFourthOrderCouplingSqCandidateAt g z χ`.

The definitions of \(\mathscr D_4\) and \(\widehat a^2\) take only the
coordinate metric.  Dependency tracing through the nested Fréchet
derivatives reaches metric order four; explicit four-jet extensionality is
not yet compiled.  Matter fields,
the coupling, and an EMD equation package enter only as correctness witnesses
in the theorem below.

Define the existence locus by the displayed assumptions used in the formal
theorem: labeled real simple Ricci spectrum; positive reconstructed non-null
Maxwell magnitude; causal scalar eigenlines and nonzero amplitudes; positive
Maxwell energy; persistent strict scalar/frame signs; the stated \(C^2\)
regularity of \(g\), the selected residual and \(q^2\); a packaged
Ricci--exterior EMD witness; and the choice-free active Maxwell-complexion
wedge.  Activity is open under continuity, but no density theorem is claimed.

For correctness of every survivor, require in addition, for every accepted
scalar probe pair,

\[
  \neg\bigl(O_-=0\ \wedge\ O_+=0\bigr),                  \tag{6.1}
\]

together with its realized-branch, nonzero-amplitude, admissible-probe,
continuity, and regularity certificate.  Condition (6.1) is the unique
scalar-closure locus.  If both relative-sign scalar branches close, acceptance
alone does not identify which branch is physical.

### Theorem IV (finite coordinate necessity and certified correctness)

*Claim ledger: C8--C9; the Kaluza specialization is C11.*

Let \(g\) carry the packaged constant-coupling Ricci--exterior EMD witness on
the existence locus.  Then

\[
  \exists\chi\in\mathscr D_4(g,z),\qquad
  \widehat a^2(g,z;\chi)=a^2.                            \tag{6.2}
\]

If every accepted choice also carries the certificate above, then

\[
  \forall\chi\in\mathscr D_4(g,z),\qquad
  \widehat a^2(g,z;\chi)=a^2,                            \tag{6.3}
\]

and the finite output image is exactly \(\{a^2\}\).  In the Kaluza
normalization the necessary output is \(3\).

This theorem is compiled in Lean.  The Kaluza statement is necessary, not a
sufficient local Kaluza-uplift criterion.  The detector is local in a fixed
coordinate trivialization: equal coordinate metric germs give identical
accepted sets and raw-choice outputs.  Full nonlinear-coordinate covariance
of the complete finite construction remains open.  The explicit raw search
has \(6{,}291{,}456\) choices, a count now proved structurally in Lean.
The correctness witness used here is a Ricci--exterior EMD package: it includes
the stress/Hodge relation and both rescaled Maxwell exterior equations, but
does not itself package the scalar wave equation.

## 7. Exact evidence

The validation layer is exact symbolic computation, deliberately separate
from the Lean theorem surface.

- A boosted Schwarzschild black string checks the convention ladder and gives
  \(a_{\rm geom}^2=3\) on a repeated-root physical channel.
- An exact \(a^2=1\) dilaton black hole returns \(1\), fails the Kaluza
  selector, and has a non-Ricci-flat convention-fixed Kaluza uplift.
- A helical Schwarzschild-string reduction has a simple Ricci spectrum and
  returns \(3\) in the physical channel.  The original sample point fails the
  finite detector's causal scalar entrance.
- At the replacement point \(r=3/2,\theta=\pi/4\), the
  `vt2-complete-detector-route` artifact passes 21 exact checks.  Its
  128-slot exact quadratic quotient calculation verifies the literal selected
  scalar and residual one-jets, selected frame/coframe one-jet identities, all
  128 components of the two complete first-order channels, the exact cosine
  quotient \(A\), physical \(dA=d(\sqrt3\,C)\), the sine quotient \(B\), all
  four next-order residual components, and \(A^2+B^2=3\).  Valid square
  relations certify the zero identities; no degree-128 number-field claim is
  made.  Model, implementation, relation, and coefficient-payload hashes are
  recorded separately.
- A paired near miss preserves the point metric, first jet, Lorentz signature,
  and simple spectrum while failing a named algebraic obstruction.

The final literal-detector derivative identification is theorem mediated.
The compiled bridge
`curvatureSeedCosineField_eventuallyEq_and_coordinateDerivative_eq_of_physicalGerm`
and
`curvatureSeedCosineCoordinateDerivative_eq_doubleAngleCosine_of_physicalGerm`,
together with
`isActualMetricPhysicalConstantCouplingChannelAt_of_patch_physicalHodgeFields`
and the compiled upstream patch-selection results, is composed with the exact
helical Kaluza EMD patch/open gates.  The benchmark-specific instantiation is
a mathematical composition recorded as exact evidence; it is not a
brute-force CAS expansion of the literal quotient's second jet and is not
itself a Lean theorem instance.

No benchmark is a newly discovered exact solution.

## 8. Machine-checked anchors and evidence classes

| Statement | Anchor or source | Evidence |
|---|---|---|
| Exact complete-channel fiber classification | `canonicalFullComplexionCouplingChannels_eq_iff_shearOrbit`; `canonicalFirstOrderChannelShear_parameter_unique` | Lean |
| Active common formal metric three-jet for every \(a\) | `activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling` | Lean |
| Rescaled and physical matter-jet injectivity | `activeAmbiguityMaxwellFirstJet_injective`; `activeAmbiguityPhysicalMaxwellFirstJet_injective` | Lean |
| Four distinct real Ricci roots | `activeAmbiguityRicciSource_has_four_distinct_real_eigenpairs` | Lean |
| Common Ricci first prolongation from the symmetric metric third jet | `activeAmbiguityFormalMetricJet3_einsteinFirstProlongation`; `coordinateRicciFirstJet_minkowski_zero` | Lean |
| Polynomial metric-germ realization through order three | `activeAmbiguityPolynomialMetricGerm_realizes_threeJet` | Lean |
| Active-family closed physical Maxwell jet and compatible potential coefficient two-jet | `matrixExteriorDerivative_activeAmbiguityPhysicalMaxwellFirstJet`; `activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes` | Lean |
| Exact raw detector-choice count \(6{,}291{,}456\) | `allActualMetricDetectorChoices4_card` | Lean |
| Analytic EMD involutivity/realization extension | Kruglikov Theorem 3 plus the scalar-wave symbol summand and Cartan--Kähler | human proof using external theorem |
| Next-order equation, quotient, uniqueness | `nextOrderSineCouplingEquation_eq_zero`; `sineCouplingFromNextOrderComponent_eq`; `nextOrderSineCoupling_unique` | Lean |
| Recovery of \(a^2\) | `couplingSqFromNextOrderComponent_eq`; `fourthOrderCouplingSqCandidate_eq_physical` | Lean |
| Active-family fourth-order equality iff \(a=\pm b\) | `activeAmbiguityFourthOrderCouplingSqCandidates_eq_iff` | Lean |
| Finite accepted set and value | `acceptedActualMetricFourthOrderDetectorChoicesAt`; `actualMetricFourthOrderCouplingSqCandidateAt` | Lean definitions |
| End-to-end physical survivor | `exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd_physicalActive` | Lean |
| Arbitrary survivor on (6.1) | `actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted` | Lean |
| Singleton output image | `acceptedActualMetricFourthOrderCouplingSqValuesAt_eq_singleton_physical` | Lean |
| Fixed-coordinate germ locality | `actualMetricFourthOrderDetector_coordinateGerm_extensionality` | Lean |
| Helical replacement route through output \(3\) | `vt2-complete-detector-route` (21 exact checks) | exact symbolic plus theorem-mediated bridge; not a Lean instance theorem |

The Lean axiom audit reports only the standard logical principles used by the
development; it does not certify the external Cartan--Kähler argument or
novelty.

## 9. Prior work and novelty boundary

The problem descends from Rainich's reconstruction of electromagnetism and the
“already unified” program of Misner and Wheeler
([Rainich 1925](https://doi.org/10.1090/S0002-9947-1925-1501302-6);
[Misner--Wheeler 1957](https://doi.org/10.1016/0003-4916(57)90049-0)).
Metric geometrization of scalar and Maxwell fields is developed, for example,
by [Krongos and Torre](https://arxiv.org/abs/1503.06311).  Higher-dimensional
algebraic Rainich theory is treated by
[Bergqvist and Höglund](https://arxiv.org/abs/gr-qc/0202092), and neighboring
duality orbits in Einstein--Maxwell--scalar models by
[Herdeiro and Oliveira](https://arxiv.org/abs/2005.05354).

The analytic realization step relies on
[Kruglikov, *Involutivity of field equations*](https://arxiv.org/abs/0902.1685),
whose Theorem 3 treats source-free Einstein--Maxwell.  Our use adds the
determined scalar-wave symbol block and verifies the EMD compatibility map;
it should not be cited as though Kruglikov explicitly stated the EMD theorem.

Conditional on the stated involutivity lemma, we are unaware of a prior result
combining an active simple-spectrum solution-level common metric-three-jet
continuum across EMD couplings, the exact affine-shear classification of its
complete-channel fibers, and an explicit one-order-higher recovery whose
active-family equality fiber is exactly \(a=\pm b\).  This is a provisional
novelty statement, not a priority claim.  Specialist review in formal PDE,
Rainich theory, and EMD geometry is required before submission.

## 10. Limitations and next theorem

The present work does not establish:

- factorization of the complete construction through an explicit coordinate
  four-jet (the compiled locality theorem assumes equality of metric germs);
- full nonlinear-coordinate covariance of the complete finite accepted set;
- a concrete Lean inhabitant of every physical-patch and per-survivor
  certificate used by the abstract detector theorems;
- detector confluence where both scalar branches close;
- the inactive, null, zero-trace, repeated-root, or collision branches;
- a converse turning every accepted metric branch into an EMD solution;
- a new closed-form Kaluza spacetime.

For the converse, after reconstructing \(B\) one must impose

\[
  dB=2A\left(\eta-\frac B2Jv\right),\qquad
  d(A^2+B^2)=0.
\]

Directly differentiating the quotient for \(B\) may require a metric five-jet.
Once the physical EMD realizer is reconstructed, the repository already
contains the conditional local Ricci-flat Kaluza uplift, converse reduction,
and presentation-orbit theorem.  Its current realizer interface explicitly
assumes that the realized fields satisfy the complete EMD equations, and no
concrete inhabitant of that full interface is compiled.  The convention-fixed
warp constants are verified, not uniquely solved from a general warp ansatz.
Removing those two conditional handoffs is part of the next paper-scale
recognition theorem; it is not folded into the result proved here.
