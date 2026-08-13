# Research plan: sharp metric-jet identifiability for the EMD coupling square

Date: 2026-08-13

Status: canonical operational plan

## 1. Material goal

The paper should establish an exact order threshold for learning the constant
Einstein--Maxwell--dilaton coupling magnitude from the metric on a genuinely
nondegenerate solution class:

> Conditional on one explicit analytic EMD involutivity lemma, there is an
> active, non-null, simple-spectrum family of local analytic EMD solution
> germs, one for every real coupling \(a\), with one common metric three-jet.
> Therefore no metric-three-jet rule identifies
> \(a^2\) on this family.  One metric derivative later, the physical
> curvature-normalized channel recovers \(a^2\).  Under explicit finite
> entrance and survivor certificates, a metric-only fourth-order coordinate
> detector contains the physical value and has singleton output.

This order-separation theorem is the north star.  It is both more defensible
and more consequential than an open-ended hunt for a new closed-form Kaluza
metric: it identifies a previously hidden obstruction, gives a finite
compatible realization, reduces the analytic upgrade to one audit lemma, and
supplies the matching recovery mechanism.

## 2. Canonical theorem hierarchy

### T1. Exact complete-channel fiber theorem

The first differentiated seed channels determine

\[
  A=a\cos(2\theta),\qquad
  \eta=d\theta+\frac B2Jv,\qquad B=a\sin(2\theta),
\]

have fibers given by

\[
  B\mapsto B+\tau,\qquad
  d\theta\mapsto d\theta-\frac\tau2Jv.
\]

When the seed amplitude and scalar covector are nonzero, equality of the full
channel pair is equivalent to equality of \(A\) plus membership in one unique
affine real-shear orbit of \((d\theta,B)\).  Status: proved in Lean.  Thus the
order-three ambiguity is exactly \(\mathbb R\), but this theorem alone would
not exclude every metric-three-jet rule.

### T2. Active analytic solution-germ collision

The explicit finite data have a common metric three-jet for every \(a\), an
injectively varying Maxwell first jet, uniform activity, and four distinct real
Ricci eigenvalues.  The polynomial metric germ, Hodge identities, explicit
Ricci first prolongation, exact unweighting/closure of the physical Maxwell
first jet, and its family-specific compatible radial-gauge potential two-jet
coefficients are machine checked.  Contracted-Bianchi compatibility is the
consequence of the fully symmetric metric third jet in the human realization
argument.

The analytic upgrade is a human formal-PDE argument conditional on one
explicit EMD involutivity lemma.  Work in the pure
second-order potential variables \((g,A,\phi)\).  Extend Kruglikov's
involutivity proof for the gauge-degenerate source-free Einstein--Maxwell
potential system (Theorem 3) by the determined scalar-wave block (Lemma 4).
The exponential EMD couplings are lower order, and the EMD Noether identity
supplies the contracted-Bianchi compatibility.  Cartan--Kähler then realizes
the compatible finite data by local analytic EMD solution germs.

Status: finite algebra, metric/Ricci first prolongation, polynomial metric
germ, and potential lift in Lean.  The contracted-Bianchi contraction,
involutivity extension, and analytic realization are a specialist-audit human
proof.  Do not call this a
direct application of Kruglikov's Theorem 4, and do not use the mixed-order
\((g,F,\phi)\) system as the main proof.

### T3. Fourth-order physical-channel recovery

Constancy of \(a\) gives

\[
  dA+2B\eta-B^2Jv=0.
\]

On \(\eta\wedge Jv\ne0\), every nonzero component yields the same

\[
  B=-\frac{(dA\wedge Jv)_{ij}}
          {2(\eta\wedge Jv)_{ij}},
  \qquad a^2=A^2+B^2.
\]

Status: proved in Lean in the selected physical curvature channel.  Combined
with T2 after its involutivity lemma is audited, this is the sharp
third-versus-fourth-order separation.  A second compiled theorem shows that,
on the explicit active formal family, two fixed fourth-order outputs agree iff
\(a=\pm b\).  In that precise family the \(\mathbb R\)-fiber at order three is
reduced to the orientation-free \(\mathbb Z_2\) at order four.  The persistent
coupling sign reflects the scalar-orientation symmetry used in the paper; this
sentence is a mathematical interpretation, not a newly packaged all-order
Lean theorem.  The recovery result is not a standalone proof of covariance
for the complete finite accepted set.

### T4. Finite coordinate detector

The finite constructor enumerates scalar probes, scalar relative sign,
principal-frame probes, coframe pivots, orientation, and source/wedge
components.  Dependency tracing through its nested Fréchet derivatives
reaches metric order four; explicit extensionality through a packaged
coordinate four-jet remains open.  Its raw search size is exactly
\(6{,}291{,}456\), now proved structurally in Lean.

- On the packaged active-regular Ricci--exterior EMD locus, at least one
  accepted choice returns physical \(a^2\).
- If every accepted choice has the explicit physical-branch, nonzero-amplitude,
  admissible-probe, continuity, regularity, and unique scalar-closure
  certificate, every survivor returns \(a^2\) and the image is \(\{a^2\}\).

Status: proved in Lean with those hypotheses.  Do not shorten the second
bullet to an unconditional “every survivor” claim.

### T5. Kaluza consequence

The convention-fixed five-dimensional vacuum reduction selects \(a^2=3\).
Thus the detector gives a necessary local Kaluza selector.  The repository's
uplift result remains conditional on an accepted EMD field realizer; detector
output \(3\) is not by itself a metric-only converse.  In the current
interface, `realize_emd` already supplies the complete EMD equations and no
concrete inhabitant of that full realizer package is compiled.  The fixed
warp constants are verified in Lean, not proved unique in a quantified
general warp ansatz.

## 3. Evidence classes

- **Lean:** finite algebra, jet identities, the symmetric metric/Ricci first
  prolongation, polynomial metric-jet realization, active-family closed
  physical Maxwell/potential two-jet, shear obstruction, physical
  fourth-order recovery, finite detector necessity/correctness, and stated
  conditional uplift modules.
- **Human proof plus external theorem:** involutivity of analytic EMD in
  potentials and realization of the compatible collision jets.
- **Exact symbolic evidence:** convention tests and physical benchmarks in
  `validation/`, including the 21-check helical fourth-order route; these are
  not Lean theorems.
- **Open:** explicit four-jet factorization (current locality is germ-based),
  a concrete Lean inhabitant of the full physical/survivor packages, full
  detector chart covariance, metric-only converse, density of the active
  locus, degenerate branches, and global reconstruction.

## 4. Publication workstream

### P0. Freeze the claim surface

- Treat `papers/coupling-detector/MANUSCRIPT.md` as the only paper narrative.
- Treat `papers/coupling-detector/TECHNICAL_SUPPLEMENT.md` as derivations and
  hypotheses, not a competing paper.
- Treat `docs/CLAIM_LEDGER.md` as the authoritative proved/external/open map.
- Redirect dated plans and result notes to these files.

### P1. Audit the analytic realization argument

Deliverable: a two-to-four-page proof that a formal-PDE specialist can check
line by line, with the explicit potential jet, symbol sequence, lower-order
perturbation statement, Noether identity, admissibility, and exact
Cartan--Kähler conclusion.  Obtain at least one independent specialist review
before submission.

### P2. Positive detector benchmark -- complete

At the generic helical-string replacement point, 21 exact checks now verify
the literal selected scalar/residual/frame one-jets, all 128 complete-channel
components, \(A\), physical \(dA=d(\sqrt3 C)\), \(B\), the complete next-order
residual, and output \(3\), using a 128-slot exact quadratic quotient
representation rather than a claimed degree-128 number-field basis.  The
artifact records separate model, implementation, relation, and coefficient
payload hashes.  The final equality between the literal quotient
derivative and physical \(dA\) is a theorem-mediated composition of the
compiled physical-germ bridge and the exact helical Kaluza EMD patch/open
gates.  It is not an independently expanded second-jet CAS identity or a
benchmark-specific Lean theorem instance.  Keep this result artifact-backed
and in the exact-symbolic evidence class.

### P3. Submission hardening

- Run `lake build` and `bash scripts/audit.sh` from a clean checkout.
- Run `validation/audit.sh` with pinned dependencies.
- Check every manuscript claim against the ledger and every theorem name
  against the compiled environment.
- Seek separate reviews for formal PDE, Rainich/EMD geometry, and Kaluza
  conventions.
- Use provisional novelty language until the literature review is independently
  checked.

## 5. Next landmark after submission

Pursue the converse only after P1--P3.  The next equations are

\[
  dB=2A\left(\eta-\frac B2Jv\right),\qquad
  d(A^2+B^2)=0.
\]

They test whether a recovered fourth-order value extends as a constant EMD
coupling and may require metric derivatives through order five.  A successful
converse would connect metric-only acceptance to the existing scalar,
Maxwell-potential, and local Kaluza-uplift modules.

## 6. Explicit non-goals for the current paper

- a new closed-form exact EMD or Kaluza spacetime;
- a global circle bundle or global topology theorem;
- complete classification of null or repeated-root branches;
- density of the active locus;
- full nonlinear-coordinate covariance of the complete finite detector;
- unconditional sufficiency of \(a^2=3\) for a Kaluza uplift.

New work should be accepted only if it closes P1, P2, or P3, or directly
strengthens T1--T5 without enlarging the paper's claim surface.
