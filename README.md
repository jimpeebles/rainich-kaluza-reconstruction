# Rainich--Kaluza reconstruction

This repository studies a coupled inverse problem in mathematical relativity:

> Can a four-dimensional Lorentzian metric determine the scalar and Maxwell
> fields of Einstein--Maxwell--dilaton theory, identify the coupling magnitude,
> and recognize the distinguished \(a^2=3\) sector obtained from
> five-dimensional vacuum Kaluza gravity?

The current result reaches a sharp metric-jet order barrier on an explicit
active, simple-spectrum class.  The solution-germ upgrade now has a
proposition-level EMD involutivity argument, backed by an independent exact
rational symbol certificate, but it still depends on Kruglikov's published
Spencer calculation and analytic Cartan--Kähler realization and is pending a
formal-PDE specialist audit.  The repository also gives a finite fourth-order
coordinate detector under stated regularity and correctness hypotheses.

## Main result

Let \(v=d\phi\), let \(J\) be the normalized non-null Maxwell-stress
involution, and write a physical curvature-normalized Maxwell field as a
duality rotation of its canonical curvature seed.  The complete first
differentiated seed channels determine

\[
  A=a\cos(2\theta),\qquad
  \eta=d\theta+\frac{a\sin(2\theta)}2Jv,
\]

have fibers that are exactly the free affine shear orbits

\[
  B\mapsto B+\tau,qquad
  d\theta\mapsto d\theta-\frac\tau2Jv,
  \qquad B=a\sin(2\theta).
\]

More precisely, when the canonical seed amplitude and scalar covector are
nonzero, two complete first-channel inputs agree if and only if their \(A\)
components agree and their \((d\theta,B)\) data differ by a unique real shear.
Thus the order-three ambiguity is an exact \(\mathbb R\)-orbit, not merely an
exhibited counterexample.

The obstruction is realized by displayed compatible truncated EMD data for every
real coupling \(a\).  The matter first jet varies injectively with \(a\), the
physical activity wedge is nonzero, and the common mixed Ricci tensor has four
distinct real eigenvalues.  The proposition-level formal-PDE argument below
upgrades these data to a local analytic EMD solution germ for every real
coupling, all with the same metric three-jet.  This conclusion is
external-theorem dependent and remains pending specialist audit.  Subject to
that audit, no function of the metric three-jet can identify \(a^2\) on this
family; in particular \(a=\sqrt3\) and \(a=1\) collide through order three.

One derivative later, constancy of \(a\) gives

\[
  dA+2B\eta-B^2Jv=0.
\]

On \(\eta\wedge Jv\ne0\),

\[
  B=-\frac{(dA\wedge Jv)_{ij}}
          {2(\eta\wedge Jv)_{ij}},
  \qquad a_{\rm geom}^2=A^2+B^2=a^2.
\]

Together with the audited analytic-realization lemma, this is the sharp
third-versus-fourth-order separation in the selected physical curvature
channel.  On the explicit active formal family, the fixed fourth-order
outputs for couplings \(a\) and \(b\) agree exactly when \(a=\pm b\): the
continuous \(\mathbb R\)-ambiguity at order three collapses to the unavoidable
orientation-free \(\mathbb Z_2\) ambiguity at order four.  The repository also
constructs a finite
coordinate detector whose only input is the metric.  Tracing its nested
Fréchet-derivative definitions reaches metric derivative order four.  A new
partial factorization packages the literal metric four-jet, proves that the
algebraic entrance already factors through its two-jet truncation, and proves
that channel acceptance and output factor through a finite operational
first-jet payload.  The remaining seam is the explicit chain-rule theorem
showing that equality of metric four-jets determines both the full upstream
entrance and the rest of that derived payload.  The first nonlinear layer is
now compiled: the actual Fréchet derivative of the composed Ricci tensor is
the algebraic Ricci first-jet evaluator on the genuine metric three-jet, and
equal literal four-jets give equal Ricci one-jets.  A
structural Lean theorem proves that it filters exactly (6{,}291{,}456) raw
choices.  A
packaged physical Ricci--exterior EMD witness on the explicit active regular
locus proves that its accepted set contains \(a^2\).  Every accepted survivor
has that value only when its displayed realized-branch, probe, regularity, and
unique scalar-closure certificate is supplied.  At Kaluza coupling the
necessary selector is \(3\); sufficiency for a Kaluza uplift is not claimed.

## Evidence boundary

The following pieces are machine checked in Lean:

- the exact classification of complete first-channel fibers as unique affine
  real-shear orbits, and the \(\mathbb R\)-to-\(\mathbb Z_2\) separation on the
  active formal family;
- the active common formal metric three-jet for every coupling;
- injectivity of the matter first jet, exact activity, simple real Ricci
  spectrum, and the common Ricci first prolongation from a fully symmetric
  metric third jet;
- realization of the common metric three-jet by an actual cubic metric field,
  an open symmetric nondegenerate determinant-negative neighborhood, and
  equality of its genuine point Ricci tensor and composed-Ricci Fréchet
  derivative with the prescribed common source and source first jet;
- exact unweighting and closure of the active physical Maxwell first jet and
  its family-specific radial-gauge potential two-jet, now realized by an
  actual quadratic one-form field with genuine nested Fréchet derivatives and
  the required differentiated curl;
- the next-order quotient, component independence, and recovery of \(a^2\);
- the finite metric-only coordinate detector, physical nonemptiness, certified
  survivor correctness, and fixed-coordinate germ locality;
- the conditional local Kaluza uplift and presentation orbit from an accepted
  EMD realizer.

The detector's compiled locality theorem is germ-based.  Its finite
four-jet/operational-jet factorization is now isolated, but the chain-rule
bridge beyond the now-compiled Ricci one-jet layer, the full upstream bridge,
and full chart covariance remain open.
The actual and finite-jet Ricci evaluators explicitly force `Matrix.inv`, and
definitionally checked regression theorems guard against accidental
entrywise inversion on the matrix's underlying function type.
The conditional uplift realizer already supplies complete EMD
equations, and the fixed warp constants are verified rather than proved
unique in a general ansatz.

The promotion from compatible finite jets to local analytic EMD solution germs
uses Cartan--Kähler theory and a short potential-variable symbol extension of
[Kruglikov's Einstein--Maxwell involutivity
theorem](https://arxiv.org/abs/0902.1685).  Kruglikov does not state this EMD
specialization verbatim: the proposition-level argument combines his
source-free Einstein--Maxwell potential block with the determined scalar-wave
block and checks the complete Maxwell-gauge and EMD Noether/Bianchi
compatibility space.  An exact rational certificate independently finds
Cartan characters \((60,45,25,5)\), \(\dim g_2=135\), \(\dim g_3=245\), the
predicted Hilbert growth through \(g_5\), and exhaustion of the tested left
kernels by the known syzygies.  It also extracts all 150 highest-jet columns
from the full coordinate EMD residual evaluator at the active lower jet,
reproduces the hand-built symbol entrywise for symbolic \(a\), and verifies
rank 15 there.  This certifies witness-level highest-jet regularity, but not an
independent variational derivation, lower-order Noether torsion, regularity of
every prolonged nonlinear equation manifold, all-order formal integrability,
or analytic realization.  On four tested non-null covectors the symbol kernel
is exactly the five gauge directions; two tested null covectors add two
metric, two Maxwell, and one scalar mode.  A Lorentz-orbit argument would be
needed to universalize this sampled characteristic statement.  The EMD
extension remains a human proof pending specialist audit, not
a Lean theorem.

The exact helical replacement benchmark now closes its final fourth-order
route with 21 checks.  Its 128-slot exact quadratic quotient calculation
verifies the selected scalar, residual, and frame one-jets, every component of
both complete channels, \(A\), the physical derivative
\(dA=d(\sqrt3\,C)\), \(B\), the next-order residual, and output \(3\).  The
128 slots are a reduction representation, not a claimed proof of a
degree-128 number field.  The artifact separately hashes its symbolic model,
implementation sources, quotient relations, and coefficient payload.  The
identification of the literal quotient derivative with physical \(dA\) uses
the compiled physical-germ bridge together with the exact helical EMD
patch/open gates; it is a theorem-mediated benchmark composition, not a
brute-force second-jet CAS expansion and not a compiled Lean instance theorem.

The repository does **not** yet prove full nonlinear-coordinate covariance of
the finite accepted set, a metric-only converse, or the degenerate branches.
It contains no new closed-form exact spacetime.

## Start here

- [Paper manuscript](papers/coupling-detector/MANUSCRIPT.md) -- canonical
  scientific narrative and theorem hierarchy.
- [Technical supplement](papers/coupling-detector/TECHNICAL_SUPPLEMENT.md) --
  detailed derivations and hypotheses.
- [Claim ledger](docs/CLAIM_LEDGER.md) -- exact proved/external/open boundary.
- [Research plan](docs/RESEARCH_PLAN.md) -- one operational north star and next
  gates.
- [Documentation map](docs/README.md) -- canonical, supporting, and archived
  files at a glance.
- [Conventions](docs/EMD_CONVENTION.md) -- normalization and field-equation
  provenance.
- [Literature map](docs/LITERATURE_MAP.md) -- prior work and provisional
  novelty boundary.
- [Companion results](docs/COMPANION_RESULTS.md) -- ranked formal results that
  support future papers without enlarging this paper's headline claim.
- [Adversarial review response](docs/ADVERSARIAL_REVIEW_RESPONSE.md) --
  signature-level findings, completed repairs, and remaining gates.
- [Validation guide](validation/README.md) -- exact symbolic evidence, kept
  separate from the Lean theorem surface.

## Reproduce

Install `elan`, then run:

```sh
lake update
lake exe cache get
lake build
bash scripts/audit.sh
```

The audit builds with warnings treated as errors, rejects placeholders and
project axioms on the advertised theorem surface, and prints the axiom
dependencies of the headline Lean theorems.

Run the exact symbolic validation separately:

```sh
cd validation
./audit.sh
```

The Python and SymPy versions are pinned.  The suite uses exact arithmetic and
rejects byte-level drift in committed artifacts.  These computations are
evidence and regression tests, not Lean proofs.

## Repository map

- `RainichKaluza/` -- formal definitions and Lean theorems.
- `papers/coupling-detector/` -- active paper and technical supplement.
- `validation/` -- pinned exact-symbolic benchmarks.
- `docs/` -- conventions, claim boundary, literature, and active research plan.
- `papers/paper-01/` and dated phase documents -- archived historical tracks;
  they are not sources of current claims or tasks.

The project is intended as a focused reconstruction theorem, not a new
unified-field proposal.  Priority language remains “we are unaware of” until
specialists in formal PDE, Rainich theory, and EMD geometry review the result.
