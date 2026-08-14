# Methodology: audit-gated, adversarially reviewed development

Date: 2026-08-14

Status: process documentation.  It describes how the repository is built and
checked; it is not evidence for any mathematical claim.

## How this repository is developed

The mathematics in this repository is developed with heavy AI assistance
under a fixed discipline: **nothing counts unless a machine or an explicit
ledger row says exactly what it is.**  The discipline has four load-bearing
parts.

1. **Hard verification gates.**  Every push builds all Lean modules against
   pinned Lean/Mathlib (`lean-toolchain`, `lakefile.toml`) with warnings as
   errors.  `scripts/audit.sh` rejects any `sorry`, `admit`, or project
   `axiom` in the source and prints the axiom dependencies of the advertised
   theorem surface (`RainichKaluza/AxiomAudit.lean`, 1,056 entries) so that
   only Mathlib's standard logical axioms appear.  The validation suite is
   pinned (`uv.lock`, exact SymPy/Python versions), floating-point free by
   an AST-level and regex audit (`rk_validation/no_approx.py`), and
   byte-reproducible: committed artifacts must be regenerated exactly, and
   they embed input, symbolic-model, and implementation hashes
   (`rk_validation/provenance.py`).

2. **The claim ledger.**  [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md) partitions
   every statement into four evidence classes -- Lean, human + external,
   exact symbolic, open -- with per-claim boundaries and an explicit list of
   prohibited upgrades.  Documents defer to it by construction, and results
   do not appear in the README or manuscript before their ledger row.

3. **Adversarial review cycles.**  The repository is periodically audited at
   the signature level -- definitions, hypothesis inventories, circularity,
   vacuity, validation arithmetic -- by independent review passes, and the
   findings are answered in writing with repairs
   ([`ADVERSARIAL_REVIEW_RESPONSE.md`](ADVERSARIAL_REVIEW_RESPONSE.md) is
   one dated snapshot).  Findings become regression locks where possible
   (for example `MatrixInverseRegression.lean`).

4. **A declared human boundary.**  One step -- the analytic EMD
   involutivity/realization argument in
   [`ANALYTIC_EMD_REALIZATION.md`](ANALYTIC_EMD_REALIZATION.md) -- is a
   human proof using a cited external theorem.  It is never described as
   machine-checked; an exact rational symbol/Cartan certificate
   (`validation/` V5) supports but does not replace the pending independent
   specialist audit.

## What this does and does not establish

The gates make the *formal* layer trustworthy to the extent one trusts Lean,
Mathlib, and the stated hypotheses of each theorem: statements must be read,
not just counted.  The gates do not certify novelty, physical relevance,
non-vacuity of hypothesis packages that lack compiled witnesses (tracked
explicitly as open items), or the human-proof step.  Anyone auditing the
repository is invited to start from `scripts/audit.sh`, the ledger, and the
theorem statements named there.
