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

The initial Lean development proves only the finite-dimensional coefficient
algebra underlying the candidate Ricci fingerprint:

- expansion of the proposed characteristic factorization;
- existence of the protected `±q` polynomial roots;
- vanishing of `C_KK = e₁²e₄ - e₁e₂e₃ + e₃²` for factored data;
- recovery of `q² = -e₃/e₁` on the nonzero-trace branch;
- an exact perfect-fluid-spectrum adversarial check;
- an explicit obstruction-zero false positive with no real protected pair,
  proving that the polynomial condition alone is insufficient.

These statements are necessary algebraic groundwork. They do **not** yet prove
that the fingerprint is sufficient, that a scalar gradient exists, that the
residual tensor has a Maxwell square root, or that a metric uplifts to a
five-dimensional Ricci-flat geometry.

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

GitHub CI additionally requests independent checking through `nanoda` while
forbidding `sorryAx`.

## Repository map

- `RainichKaluza/`: machine-checked definitions and theorems.
- `docs/RESEARCH_STATE.md`: inherited results, corrections, and open questions.
- `docs/CLAIM_LEDGER.md`: exact claim classification and proof obligations.
- `docs/LITERATURE_MAP.md`: relation to known reconstruction results.
- `docs/VIBEMATHED_POSITIONING.md`: publication narrative and Lean contract.
- `papers/paper-01/OUTLINE.md`: first-paper theorem architecture.
- `RainichKaluza/AxiomAudit.lean`: printed axiom dependencies for advertised
  theorems.
- `ROADMAP.md`: staged research program.
