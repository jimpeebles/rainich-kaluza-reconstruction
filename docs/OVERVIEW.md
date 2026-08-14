# Overview for physicists

Date: 2026-08-14

Status: informal on-ramp.  Every claim below is bounded by
[`CLAIM_LEDGER.md`](CLAIM_LEDGER.md); where this page and the ledger differ,
the ledger wins.

## The question

Einstein--Maxwell--dilaton (EMD) theory carries one constant coupling
$a$ in the action term $e^{a\phi}F^2$.  Five-dimensional vacuum gravity,
reduced along a circle in Kaluza's sense, lands exactly on $a^2=3$; the
low-energy string sector sits at $a^2=1$; Reissner--Nordstrom at $a=0$.
The question this repository answers locally, on an explicit nondegenerate
branch, is: **can the spacetime metric alone tell you $a^2$ -- and how many
derivatives does it take?**

This is the classical Rainich--Misner--Wheeler "already unified" program
pointed at the sector Kaluza distinguished.  Rainich reconstructed the
Maxwell field from curvature; later work geometrized scalar fields; the
coupled scalar--Maxwell system resists both, because the Ricci tensor mixes
the two contributions and the coupling only enters after differentiation.

## The answer (active, non-null, simple-spectrum branch)

There is a sharp derivative-order threshold with an exact symmetry structure:

- **Order two.**  Curvature determines the stress split, the Maxwell
  magnitude, and the scalar line -- but not the coupling.
- **Order three.**  The complete differentiated Maxwell-seed channels
  determine $A=a\cos2\theta$ and one covector $\eta$, and *provably
  nothing more*: the fibers are exactly a free one-parameter affine "shear"
  group mixing the hidden component $B=a\sin2\theta$ with the duality-angle
  gradient.  The third-order ambiguity is exactly $\mathbb R$.  An explicit
  family of truncated EMD data -- one member for every real $a$, all with
  the *same* metric three-jet -- realizes the obstruction (compiled
  impossibility theorem; the upgrade from finite jets to analytic solution
  germs is a written formal-PDE argument pending specialist audit, supported
  by an exact symbolic symbol/Cartan certificate).
- **Order four.**  Constancy of $a$ gives $dA+2B\eta-B^2Jv=0$; one wedge
  eliminates the quadratic term and recovers $B$, hence
  $a^2=A^2+B^2$, component-independently.  On the explicit family the
  continuum collapses exactly to the unavoidable sign: outputs agree iff
  $a=\pm b$.  A finite metric-only detector (6,291,456 raw choices,
  machine-counted) implements the recovery with compiled correctness
  theorems under explicit entrance and certificate hypotheses.
- **Kaluza selector.**  On an accepted Kaluza branch the necessary output is
  $3$.  Necessity only: output $3$ is *not* claimed sufficient for a
  five-dimensional origin.

A blunt paraphrase, with its caveat: a local observer measuring curvature
and one covariant derivative cannot determine the hidden-sector coupling; two
derivatives suffice on this branch.  The compiled detector is
fixed-coordinate, so the covariant paraphrase is heuristic until the chart
covariance program closes.

## Why a physicist might care

1. **A new kind of invariant.**  "At which jet order does a Lagrangian
   constant become observable, and what is the exact ambiguity group below
   that order" is an identifiability question with almost no relativity
   literature.  Here it has a complete answer on one branch:
   $\mathbb R$ at order three, $\mathbb Z_2$ at order four.
2. **The mechanism.**  The coupling hides precisely along the duality
   direction, in the kernel of the Maxwell-stress first variation -- a
   finite-dimensional, checkable sharpening of the folklore that duality
   orbits confound coupling identification.
3. **The Kaluza arc.**  The forward program
   ([`KALUZA_ARC_PLAN.md`](KALUZA_ARC_PLAN.md)) aims at the local
   recognition theorem: curvature conditions necessary *and sufficient* for
   a metric to be a Kaluza reduction, with the Ricci-flat uplift delivered
   constructively.  The converse skeleton (Bianchi/Noether-forced scalar
   equation, half-angle phase reconstruction) is partially compiled and
   fully conditional; see the plan for exact boundaries.

## What is machine-checked, and what is not

About 48k+ lines of Lean 4 over Mathlib: no `sorry`, no project axioms, a
1,056-entry `#print axioms` audit, CI with warnings-as-errors.  Separately, a
pinned exact-arithmetic SymPy suite (no floating point anywhere) supplies
convention oracles and the Cartan-character certificate for the one external
dependency.  Machine-checked does **not** cover: the analytic solution-germ
upgrade (human proof pending specialist audit), full chart covariance of the
detector, density of the active branch, the degenerate (null,
repeated-root) strata containing the textbook spherical solutions, any
sufficiency of output $3$, or novelty.  The four evidence classes and
every boundary are tabulated in [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md).

## Reading path

The formal narrative is
[`../papers/coupling-detector/MANUSCRIPT.md`](../papers/coupling-detector/MANUSCRIPT.md);
derivations and hypotheses are in the
[technical supplement](../papers/coupling-detector/TECHNICAL_SUPPLEMENT.md);
the analytic realization note for specialists is
[`ANALYTIC_EMD_REALIZATION.md`](ANALYTIC_EMD_REALIZATION.md); prior work and
the provisional novelty boundary are in
[`LITERATURE_MAP.md`](LITERATURE_MAP.md).
