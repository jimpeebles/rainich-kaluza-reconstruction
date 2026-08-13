# A shear obstruction and fourth-order recovery of the Einstein--Maxwell--dilaton coupling square from metric derivatives

## Abstract

We study whether a finite coordinate construction from a four-dimensional
Lorentzian metric can recover the squared magnitude of the constant coupling in
Einstein--Maxwell--dilaton (EMD) theory.  On an active non-null Ricci branch,
the complete first differentiated Maxwell--Rainich seed channels determine
two effective variables

\[
  A=a\cos(2\theta),\qquad
  \eta=d\theta+\frac{a\sin(2\theta)}2Jv,
\]

where \(v=d\phi\) and \(J\) is the normalized Maxwell-stress involution.  We
prove that these channels have an exact one-parameter shear kernel, so neither
\(B=a\sin(2\theta)\) nor \(a^2=A^2+B^2\) is identifiable from this complete
channel system at its third-order stage.  This is a lower bound for the
displayed channel construction, not for every conceivable invariant of
third-order metric data.  Constancy of \(a\) supplies one derivative later

\[
  dA+2B\eta-B^2Jv=0.
\]

On the active locus \(\eta\wedge Jv\ne0\), any nonzero component gives the
explicit, component-independent quotient

\[
  B=-\frac{(dA\wedge Jv)_{ij}}
          {2(\eta\wedge Jv)_{ij}},\qquad
  a_{\mathrm{geom}}^2=A^2+B^2.
\]

We implement this construction as a finite coordinate detector using metric
derivatives through order four.  For every metric carrying the packaged
constant-coupling Ricci--exterior EMD witness on the explicit active regular
locus, the accepted set is nonempty and contains a branch with
\(a_{\mathrm{geom}}^2=a^2\).  If, for every accepted choice, the displayed
realized-branch, nonzero-amplitude, admissible-probe, continuity, regularity,
and unique scalar-closure certificate holds, every survivor has that value;
hence the finite output image is the singleton \(\{a^2\}\).  The
unavoidable correlated symmetry \((v,a)\mapsto(-v,-a)\) makes \(a^2\), rather
than signed \(a\), the sharp sign-insensitive target.  In the Kaluza
normalization an accepted physical branch returns the necessary selector
\(3\).  The algebraic, differential, finite-selection, and correctness
constituents are machine checked in Lean.  This is a channel-system
obstruction and conditional necessity/correctness theorem, not a
diffeomorphism-covariant four-jet classification, local converse, Kaluza
recognition theorem, or new exact spacetime solution.

## 1. Convention and metric-only detector

We use signature \((-+++)\) and the convention

\[
  \mathcal L=\sqrt{-g}\left(R-\frac14e^{a\phi}F^2
                    -\frac12(\nabla\phi)^2\right).
\]

Writing \(v=d\phi\) and \(H=e^{a\phi/2}F/\sqrt2\), the mixed Ricci
endomorphism decomposes as

\[
  \mathcal R=S+V,qquad
  V=\frac12v^\sharp\otimes v,qquad
  S=\operatorname{MaxwellStress}(H),qquad S^2=q^2I.
\]

On the non-null branch \(q>0\), set \(J=S/q\).  A positive canonical
Maxwell seed \((H_0,*H_0)\) for \(S\) and a physical representative in its
duality orbit may be written

\[
  H=cH_0+s(*H_0),\qquad c^2+s^2=1.
\]

No choice of an angle is required.  The physical double-angle scalars

\[
  C=c^2-s^2,\qquad S_2=2cs
\]

are contractions of \((g^{-1},H,*H,q)\), and the complexion covector is

\[
  \omega=\frac{C\,dS_2-S_2\,dC}{2}=c\,ds-s\,dc.
\]

This expression is invariant under \((c,s)\mapsto(-c,-s)\), under
simultaneous \((H,*H)\mapsto(-H,-*H)\), and under changes of adapted frame.

For a metric \(g\) and point \(z\), let

\[
  \mathscr D_4(g,z)
\]

denote `acceptedActualMetricFourthOrderDetectorChoicesAt g z`.  It is the
finite set obtained by enumerating coordinate probes for the two scalar
eigenlines and two Maxwell principal planes, an algebraic Lorentzian pivot
recipe, the relative scalar sign, orientation, a source component, and a
wedge component, then filtering by explicit metric equations and strict
inequalities.  For \(\chi\in\mathscr D_4(g,z)\), write

\[
  \widehat a^2(g,z;\chi)
\]

for `actualMetricFourthOrderCouplingSqCandidateAt g z χ`.

Both \(\mathscr D_4\) and \(\widehat a^2\) are formulas in the coordinate
metric and its finite coordinate derivatives.  They take no matter field, scalar,
complexion, coupling, EMD equation package, or five-dimensional uplift as an
input.  Physical EMD fields appear below only as witnesses in the theorem
that proves how this metric-only coordinate detector behaves on a metric
carrying the stated Ricci--exterior witness.  This is the same logical
distinction as that between an algorithm and the external hypothesis used to
prove its correctness.

The coordinate derivative bookkeeping is: Ricci uses metric derivatives
through order two, the complete seed exterior channels use one further
derivative, and \(dA\) uses one more.  Thus \(\mathscr D_4\) is a finite
coordinate construction using derivatives through order four.  The current
formalization does **not** prove that the whole accepted-set construction is
an invariant function of an abstract four-jet under arbitrary nonlinear
coordinate changes.  The proved frame, orientation, and physical-active
invariances are narrower statements and should not be conflated with full
diffeomorphism covariance.  In the formal theorem, regularity is recorded
directly for the constructed metric, residual, and \(q^2\) fields.

## 2. The active regular locus

The hypotheses are displayed rather than summarized by a claim of genericity
or open density.  The formal result is conditional on two nested active
regular loci.

### 2.1 Existence locus \(\mathcal A_{\mathrm{exist}}\)

At \(z\in U\), the nonemptiness theorem assumes:

1. **Lorentzian algebraic entrance.**  The mixed Ricci endomorphism is on the
   selected real simple-spectrum branch; the reconstructed \(q^2\) is
   positive; the polynomial projectors obey the tested rank, idempotence,
   complementarity, self-adjointness, and reconstruction equations; and the
   metric has index one.
2. **Realized scalar branch.**  A curvature scalar-jet branch is realized on
   the open patch \(U\).  Its two spectral amplitudes are nonzero at \(z\),
   one finite timelike/spacelike probe pair has the required strict signs,
   and the relevant diagonal amplitudes are positive and continuous.  The
   selector theorem then proves that one literal relative-sign covector
   agrees locally with the physical scalar covector up to a common sign; this
   scalar germ is a conclusion, not an extra detector premise.
3. **Persistent finite frame.**  The selected projector pairings and coframe
   entries are continuous at \(z\), so the same finite scalar/frame/Hodge
   choice remains upstream on a neighborhood.  The upstream gates imply a
   pseudo-orthonormal coframe with positive determinant.
4. **Conventional regularity.**  On \(U\), \(g\) and the reconstructed \(q^2\)
   have the displayed \(C^2\) regularity.  For each choice that the upstream
   selector can return, its metric-constructed Maxwell residual is \(C^2\).
   These data, rather than a bespoke frame hypothesis, imply \(C^2\)
   regularity of the selected coframe and of the protected positive \(q\).
5. **Choice-free active wedge.**  Let \(S_{\rm phys}\) be the physical
   Maxwell stress and let
   \(\omega_{\rm phys}=(C\,dS_2-S_2\,dC)/2\).  Then

   \[
      \omega_{\rm phys}\wedge S_{\rm phys}^{T}v\ne0
      \quad\text{at }z.
   \]

   Under the preceding hypotheses this is equivalent to the selected
   detector gate \(\eta\wedge Jv\ne0\).  It is invariant under frame change,
   physical-pair sign, and scalar orientation.  The component quantifier is
   existential: some enumerated wedge component must be nonzero.  Requiring
   every component would be impossible because each diagonal component
   \((i,i)\) vanishes identically.  For continuous \(S_{\rm phys}\),
   \(\omega_{\rm phys}\), and \(v\), Lean also proves that this active set is
   open and that activity at one point persists on a neighborhood.  No
   density claim is made.
6. **Physical correctness witness.**  On \(U\), there exists the packaged
   choice-independent Ricci--exterior EMD witness: \(C^1\) fields \((H,*H)\)
   whose stress is the Maxwell term in the Ricci decomposition, whose second
   field is the metric Hodge dual of the first, and which satisfy the two EMD
   exterior equations with the physical scalar covector and one constant
   signed coupling \(a\).  This package does not explicitly contain the
   dilaton scalar equation, so it must not be described as a complete EMD
   solution package.

Items 1--5 are the regular/nondegenerate route through the finite detector.
Item 6 is not supplied to the detector; it is the Ricci--exterior witness
used only in the necessity proof.

### 2.2 Accepted-branch identifiability locus \(\mathcal A_{\mathrm{id}}\)

For correctness of *every* accepted survivor, add the following condition for
each accepted scalar probe pair \((i,j)\):

\[
  \neg\bigl(O_{ij,-}(z)=0\ \wedge\ O_{ij,+}(z)=0\bigr),
  \tag{UC}
\]

where \(O_{ij,\pm}\) are the two literal metric scalar-closure
obstructions.  This is
`IsActualMetricUniqueScalarClosureBranchAt4 g z i j`.  Each survivor is also
required to lie on its realized, nonzero-amplitude scalar-jet patch with the
displayed admissible-probe, frame-continuity, coframe-\(C^2\), and
magnitude-\(C^2\) hypotheses.

Condition (UC) is sharp for the present scalar-branch selection argument.  A
Ricci--exterior witness together with the realized-jet, algebraic,
admissible-probe, and nonzero-amplitude hypotheses ensures that at least one
relative-sign branch is the closed physical scalar branch.  If both literal branches close, pointwise
metric acceptance alone does not identify which one is physical.  We
therefore make no unconditional all-survivor claim on that exceptional locus.

## 3. Main theorem

### Theorem (active-regular fourth-order coordinate coupling recovery)

Let \(g\) be a Lorentzian metric on an oriented coordinate patch \(U\), let
\(z\in U\), and construct the finite metric-only set
\(\mathscr D_4(g,z)\) and its values \(\widehat a^2(g,z;\chi)\).

1. **Necessity and nonemptiness.**  If \(g\) carries on \(U\) the packaged
   constant-coupling Ricci--exterior EMD witness with coupling \(a\), and
   \((g,z)\in\mathcal A_{\mathrm{exist}}\), then

   \[
     \exists\chi\in\mathscr D_4(g,z),\qquad
     \widehat a^2(g,z;\chi)=a^2.
   \]

2. **All-survivor correctness within the coordinate construction.**  If in
   addition every accepted choice carries its probe-specific realized branch,
   nonzero amplitudes, algebraic/probe signs, frame and diagonal continuity,
   coframe/magnitude regularity, and unique-closure certificate in
   \(\mathcal A_{\mathrm{id}}\), then

   \[
     \forall\chi\in\mathscr D_4(g,z),\qquad
     \widehat a^2(g,z;\chi)=a^2.
   \]

   Combining this with part 1, the finite output-value set is exactly the
   singleton \(\{a^2\}\).  In particular, any two accepted choices agree even
   if they use different scalar probes, scalar signs, Maxwell frames,
   orientations, source components, or wedge components.
3. **Kaluza necessary-selector corollary.**  In the
   five-to-four-dimensional Kaluza
   normalization \(a^2=3\), part 1 produces an accepted branch with value
   \(3\); on \(\mathcal A_{\mathrm{id}}\), every accepted branch has value
   \(3\).  This is a necessary selector for the Kaluza-coupled
   Ricci--exterior sector, not a sufficient recognition theorem for a Kaluza
   uplift.

Part 1 is a compiled end-to-end Lean theorem.  Part 2 is compiled both as
pointwise per-choice correctness/pairwise equality and as an exact singleton
finite-image theorem whose premise supplies the displayed certificate for
every survivor plus nonemptiness.  Open-patch confluence is also compiled.
The theorem does not assert that a metric passing the finite tests
admits a complete EMD realization, nor does it establish nonlinear-coordinate
covariance of the full accepted-set construction.  Those are separate
problems.

## 4. Why the present third-order channels fail and the next-order channel succeeds

Put

\[
  A=a\cos(2\theta),\qquad B=a\sin(2\theta),\qquad
  \eta=d\theta+\frac B2Jv.
\]

The complete pair of first seed-derivative three-form channels is injective
in the *effective* variables \((\eta,A)\), provided the seed and scalar source
are nonzero.  It is not injective in the physical variables
\((d\theta,B)\).  For every \(\tau\in\mathbb R\),

\[
   B\longmapsto B+\tau,
   \qquad
   d\theta\longmapsto d\theta-\frac\tau2Jv
\]

leaves \((\eta,A)\), hence the complete channel pair, unchanged.  This is an
exact kernel of the full channels, not a failure caused by an unfortunate
probe.  Since changing \(B\) changes \(A^2+B^2\) in general, \(a^2\) is not
identifiable from this complete first differentiated seed-channel system.
This theorem does not exclude a different, presently unknown construction
from other metric derivatives through order three.

For constant \(a\), differentiating \(A=a\cos(2\theta)\) and eliminating
\(d\theta\) gives

\[
  dA+2B\eta-B^2Jv=0.                 \tag{1}
\]

Wedging (1) with \(Jv\) removes the quadratic term.  Whenever
\(\Delta_{ij}=(\eta\wedge Jv)_{ij}\ne0\),

\[
  B=-\frac{(dA\wedge Jv)_{ij}}{2\Delta_{ij}}.          \tag{2}
\]

All unused components of (1) remain obstruction tests.  Lean proves that any
two accepted nonzero components give the same \(B\), so (2) is a chart of one
component-independent value within this channel construction.  It also proves

\[
  \eta\wedge Jv=d\theta\wedge Jv,
\]

which makes the active locus independent of the hidden \(B\) and of \(a\).
Finally, the double-angle identity gives

\[
  A^2+B^2=a^2.
\]

This obstruction/recovery pair is the conceptual result: within this channel
system, the fourth-order formula is not a repaired third-order ansatz but the
first added derivative that breaks its exact lower-order shear symmetry.

## 5. Sharp scope and exceptions

The theorem deliberately excludes:

- the null or zero Maxwell-stress locus \(q=0\);
- repeated or nonreal Ricci spectral branches and vanishing scalar
  amplitudes;
- failed strict frame/probe signs or loss of the selected smooth chart;
- the inactive locus \(\eta\wedge Jv=0\), where equation (2) has no
  nonzero denominator;
- unconditional identification of all survivors when both relative-sign
  scalar branches close;
- a converse claiming that every accepted metric branch integrates to an
  EMD solution;
- a claim that the full finite coordinate detector is already known to be
  covariant under arbitrary nonlinear chart changes.

The scalar orientation ambiguity is not a technical defect.  The correlated
replacement \((v,a)\mapsto(-v,-a)\) preserves the exterior EMD system and its
metric geometry, while the detector output is unchanged.  Related
geometry-preserving coupling/duality orbits are known in broader
Einstein--Maxwell--scalar models.  Thus the sharp sign-insensitive target of
this reconstruction is \(a^2\).

A complete local recognition theorem would additionally have to construct a
single local complexion and constant coupling from an arbitrary accepted
branch.  In the present variables it must recover the complementary relation

\[
  dB=2A\left(\eta-\frac B2Jv\right),
  \qquad d(A^2+B^2)=0.
\]

Direct differentiation of the quotient (2) may require coordinate metric
derivatives through order five; no order-four integrability replacement is
claimed here.  Likewise, this work does not discover a previously unknown
exact Kaluza spacetime.

The complete-detector benchmark remains open.  In particular, the previously
advertised V-T2 helical black-string sample at
\(r=3,\theta=\pi/4\) returns \(3\) in the isolated active channel formula but,
after audit, lies outside the causal scalar entrance; consequently its full
accepted set is empty.  It is not a positive benchmark for
\(\mathscr D_4\).  At \(r=3/2,\theta=\pi/4\), exact symbolic routing passes
the algebraic, radicand, selected-probe, and literal scalar-value prefix, with
the selected candidate equal to the physical \(d\phi\). Exact differentiation
of the literal root, four-root-projector, normalization, and amplitude formulas
also reduces the selected scalar-closure obstruction to zero. The remaining
upstream suffix, physical activity, and the fourth-order accepted output are
still uncertified, so this is not yet a positive complete-detector benchmark.

## 6. Machine-checked theorem map

| Paper statement | Exact Lean anchor |
|---|---|
| Complete order-three shear invariance | `canonicalFullComplexionCouplingChannels_shear_invariant` |
| Order-three noninjectivity | `canonicalFullComplexionCouplingChannels_not_injective`; `canonicalPhysicalSeedChannels_not_injective` |
| Constancy equation (1) | `nextOrderSineCouplingEquation_eq_zero` |
| Quotient (2) and uniqueness of \(B\) | `sineCouplingFromNextOrderComponent_eq`; `nextOrderSineCoupling_unique` |
| Recovery of \(a^2\) | `couplingSqFromNextOrderComponent_eq`; `fourthOrderCouplingSqCandidate_eq_physical` |
| Finite component selection on the active wedge | `exists_fourthOrderComponentChoice_iff_activeWedge`; `exists_actualMetricGenericFourthOrderComponentAt_withChannel_iff` |
| Complete finite coordinate accepted set and value | `acceptedActualMetricFourthOrderDetectorChoicesAt`; `actualMetricFourthOrderCouplingSqCandidateAt`; `mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff` |
| Scalar-orientation invariance of the output | `fourthOrderCouplingSqCandidate_neg_scalar` |
| Finite metric upstream selector and persistent germ | `exists_eventually_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch` |
| Selected regularity from conventional data | `actualMetricDetectorRegularity_of_residual` |
| Choice-free physical complexion | `physicalComplexionOneFormFromDoubleAngle_eq_dualityComplexion`; `coordinatePhysicalComplexionOneForm_changeBasis`; `coordinatePhysicalComplexionOneForm_neg_physicalPair` |
| Physical active locus equals detector active gate | `isActualMetricActiveFourthOrderWedgeAt_iff_choiceFreePhysicalScalarOrbit` |
| Openness and local persistence of the physical active locus | `isOpen_coordinateMaxwellStressActiveWedge`; `eventually_coordinateMaxwellStressActiveWedge_of_continuousAt` |
| Detector-choice-free physical Ricci--exterior witness package | `ChoiceIndependentActualMetricEMDPhysicalPatch4` |
| End-to-end nonemptiness and physical \(a^2\) | `exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd_physicalActive` |
| Pointwise correctness of an arbitrary accepted survivor on (UC) | `actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted` |
| Open-patch cross-choice confluence on (UC) | `actualMetricFourthOrderCouplingSqCandidates_eq_of_invariantEMD_uniqueClosure` |
| Pairwise pointwise confluence with per-choice certificates | `actualMetricFourthOrderCouplingSqCandidates_eq_of_invariantEMD_pointwiseAccepted` |
| Certified survivor output | `InvariantEMDPointwiseSurvivorData4.output_eq_physical` |
| Complete finite output image is \(\{a^2\}\) | `acceptedActualMetricFourthOrderCouplingSqValuesAt_eq_singleton_physical` |
| Necessary Kaluza selector \(3\) | `exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_invariantEMD_physicalActiveResult` |

The advertised anchors are included in `RainichKaluza/AxiomAudit.lean`; their
reported dependencies are the standard Lean principles already used by the
development, not untracked mathematical axioms.

## 7. Relation to prior work and novelty position

The problem descends from Rainich's curvature reconstruction of
electromagnetism and its “already unified” development by Misner and Wheeler
([Rainich 1925](https://doi.org/10.1090/S0002-9947-1925-1501302-6);
[Misner--Wheeler 1957](https://doi.org/10.1016/0003-4916(57)90049-0)).
Separate geometrization results for scalar and Maxwell fields are well
established; a modern unified treatment is
[Krongos--Torre](https://arxiv.org/abs/1503.06311).  Higher-dimensional
algebraic Rainich identities are studied by
[Bergqvist--Höglund](https://arxiv.org/abs/gr-qc/0202092).  These works do not
by themselves solve the coupled inverse problem in which scalar and Maxwell
contributions are mixed in one Ricci tensor.

The distinguished Kaluza coupling and the convention used here are documented
by [Lü--Mao--Wu](https://arxiv.org/abs/1909.00970).  Electromagnetic-duality
orbits that preserve scalar and spacetime geometry while relating coupling
functions are studied by
[Herdeiro--Oliveira](https://arxiv.org/abs/2005.05354); in the pure
exponential axion-free specialization, the surviving sign relation supports
the conclusion that \(a^2\), not signed \(a\), is the sharp sign-insensitive target.

To the extent of our focused primary-source search, we are unaware of a prior
finite coordinate construction from metric derivatives through order four
that recovers an unknown EMD coupling magnitude on this explicit active
regular locus under a Ricci--exterior witness, or of the specific exact shear
obstruction for the complete first
differentiated seed channels followed by the active-locus next-order quotient
proved here.  This is a provisional novelty position, not a priority claim
and not a universal lower-bound claim.  It should remain phrased as “we are
unaware of” until citation-chain searches and review by specialists in
Rainich theory, EMD geometry, and exact solutions are complete.

## 8. Publication status

The result is cohesive enough for a focused theorem-paper draft if its claim
is kept at the present boundary: an exact shear obstruction for one complete
third-order channel system plus a constructive finite coordinate recovery
using metric derivatives through order four, with accepted-branch correctness
on an explicit active regular locus and a necessary Kaluza selector.  The
machine-checked chain is substantially stronger than a formal algebra
exercise because it includes finite scalar/frame selection, Maxwell
stress-fibre classification, Hodge transport, physical field-germ transfer,
regularity promotion, invariant physical activity, and cross-choice
correctness.

The largest remaining exposition/formal gap is to compress the long coordinate
entrance signature into a geometric active-regular proposition and prove both
its equivalence to the displayed finite Lean gates and the required
nonlinear-coordinate covariance.  The complete benchmark must also be
replaced: V-T2 at \(r=3,\theta=\pi/4\) fails causal scalar entrance, while the
\(r=3/2,\theta=\pi/4\) candidate passes the exact prefix through its scalar
closure gate. Its remaining upstream, activity, and accepted-output suffix is
uncertified.
Closing those items would make the
theorem independently readable and computationally auditable without
inflating its mathematical scope.  Specialist novelty review is the other
pre-submission requirement.  The full local converse is a separate research
problem, not a claim of the present paper.
