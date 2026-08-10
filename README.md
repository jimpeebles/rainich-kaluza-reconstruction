# Rainich–Kaluza reconstruction

This repository investigates a precise descendant of the classical Rainich
question:

> When does a four-dimensional Lorentzian metric encode, and allow one to
> reconstruct, the coupled scalar and Maxwell fields of the
> `a = √3` Einstein–Maxwell–dilaton sector obtained from five-dimensional
> vacuum Kaluza gravity?

The project is intentionally narrower than a new unified-field proposal. Its
first goal is a necessary-and-sufficient local reconstruction theorem on a
clearly stated generic branch, together with a classification of the branches
where that theorem fails or changes form.

## Current verified surface

The Lean development currently proves the coefficient algebra underlying the
candidate Ricci fingerprint and the generic pointwise reconstruction layer:

- expansion of the proposed characteristic factorization;
- existence of the protected `±q` polynomial roots;
- vanishing of `C_KK = e₁²e₄ - e₁e₂e₃ + e₃²` for factored data;
- recovery of `q² = -e₃/e₁` on the nonzero-trace branch;
- an exact perfect-fluid-spectrum adversarial check;
- an explicit obstruction-zero false positive with no real protected pair,
  proving that the polynomial condition alone is insufficient;
- forced generic-eigenbasis scalar-block diagonals and automatic trace
  compatibility;
- exact real rank-one and Lorentzian signature-aware scalar-factorization
  criteria for the complementary two-dimensional block;
- uniqueness of scalar components for a fixed nondegenerate block up to the
  unavoidable global sign;
- a two-branch classification showing that pointwise curvature data admit a
  second, distinct scalar tensor under a relative component sign flip;
- realization of that ambiguity by an involutive spectral reflection which
  commutes with the Ricci block;
- the basis-independent square law for rank-one endomorphisms;
- a coordinate-free, noncommutative derivation of the Sylvester reconstruction
  equation, together with its invariance under Ricci-centralizing involutions.

These statements are necessary algebraic groundwork. They do **not** yet prove
that the fingerprint is sufficient, that a scalar gradient exists, that the
residual tensor has a Maxwell square root, or that a metric uplifts to a
five-dimensional Ricci-flat geometry.

The current result also corrects an earlier uniqueness expectation: on the
genuinely two-component generic branch, curvature algebra determines the
scalar tensor only up to a discrete spectral-centralizer action. Differential
data are therefore essential, not merely a final consistency check.

## Why this is not a left-field problem

The project sits at the intersection of three established reconstruction
programs:

1. classical four-dimensional Rainich reconstruction of electromagnetism;
2. metric-only geometrization and reconstruction of scalar fields;
3. the `a = √3` Einstein–Maxwell–dilaton system obtained by Kaluza reduction.

The possible new contribution is the coupled reconstruction problem: recover
the scalar-gradient tensor and Maxwell sector simultaneously from curvature,
including the differential and degenerate conditions needed for a genuine
if-and-only-if theorem. See [the literature map](docs/LITERATURE_MAP.md) and
[Vibemathed positioning](docs/VIBEMATHED_POSITIONING.md).

## Build

Install `elan`, then run:

```sh
lake update
lake exe cache get
lake build
```

The Lean and Mathlib releases are pinned. Publication branches must contain no
`sorry`, `admit`, or project axioms in the claimed theorem surface.

Run the stronger local audit with:

```sh
bash scripts/audit.sh
```

The audit builds with warnings treated as errors before printing the axiom
surface.

GitHub CI additionally requests independent checking through `nanoda` while
forbidding `sorryAx`.

## Repository map

- `RainichKaluza/`: machine-checked definitions and theorems.
- `docs/RESEARCH_STATE.md`: inherited results, corrections, and open questions.
- `docs/EMD_CONVENTION.md`: convention-fixed field-equation provenance.
- `docs/GENERIC_RECONSTRUCTION.md`: derivation and boundary of the current
  generic eigenbasis result.
- `docs/CLAIM_LEDGER.md`: exact claim classification and proof obligations.
- `docs/LITERATURE_MAP.md`: relation to known reconstruction results.
- `docs/VIBEMATHED_POSITIONING.md`: publication narrative and Lean contract.
- `docs/RELEASE_CHECKLIST.md`: public GitHub release boundary and audit list.
- `papers/paper-01/OUTLINE.md`: first-paper theorem architecture.
- `papers/paper-01/MANUSCRIPT.md`: self-contained public-release manuscript.
- `papers/paper-01/LEAN_MAP.md`: manuscript-to-Lean claim translation.
- `papers/paper-01/DRAFT_THEOREMS.md`: precise working statements and proof
  status for the first paper.
- `papers/paper-01/VIBEMATHED_SUBMISSION.md`: staged submission fields and
  verification disclosure.
- `RainichKaluza/AxiomAudit.lean`: printed axiom dependencies for advertised
  theorems.
- `ROADMAP.md`: staged research program.
- `RELEASE_NOTES.md`: draft pinned-release claim and verification boundary.
