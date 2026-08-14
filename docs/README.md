# Documentation map

The active research has one claim surface and one paper.  Pick a path below;
everything else is technical support, working notes, or archive.

## Start here, by reader

- **Physicist or relativist:** [`OVERVIEW.md`](OVERVIEW.md), then the
  [manuscript](../papers/coupling-detector/MANUSCRIPT.md).
- **Formalization auditor:** [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md),
  [`ARCHITECTURE.md`](ARCHITECTURE.md), then run `bash scripts/audit.sh`.
- **Formal-PDE specialist:**
  [`ANALYTIC_EMD_REALIZATION.md`](ANALYTIC_EMD_REALIZATION.md) with the
  `vt3-emd-symbol-involutivity` certificate in
  [`../validation/README.md`](../validation/README.md).

## Canonical research documents

- [`../papers/coupling-detector/MANUSCRIPT.md`](../papers/coupling-detector/MANUSCRIPT.md)
  — the sole scientific narrative.
- [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md) — the authoritative separation of Lean,
  human/external, exact-symbolic, and open claims.
- [`RESEARCH_PLAN.md`](RESEARCH_PLAN.md) — the current north star and the three
  publication gates.
- [`KALUZA_ARC_PLAN.md`](KALUZA_ARC_PLAN.md) — the post-paper recognition
  program, its K-workstreams, the live gate crosswalk, and compiled-progress
  audit notes; plans work, claims nothing.
- [`EMD_CONVENTION.md`](EMD_CONVENTION.md) — field equations and normalization.
- [`ANALYTIC_EMD_REALIZATION.md`](ANALYTIC_EMD_REALIZATION.md) — the
  specialist-audit proof note for the analytic solution-germ upgrade.
- [`LITERATURE_MAP.md`](LITERATURE_MAP.md) — prior work and provisional novelty
  boundary.
- [`COMPANION_RESULTS.md`](COMPANION_RESULTS.md) — ranked compiled results and
  follow-up directions kept outside the active paper's headline claim.

The detailed derivations and theorem-to-Lean map are in the
[technical supplement](../papers/coupling-detector/TECHNICAL_SUPPLEMENT.md).

## Working notes

- [`KALUZA_CONVERSE_DERIVATION.md`](KALUZA_CONVERSE_DERIVATION.md) — the
  zero-claim K2 derivation with compiled-status updates and remaining seams.
- [`ADVERSARIAL_REVIEW_RESPONSE.md`](ADVERSARIAL_REVIEW_RESPONSE.md) — dated
  snapshot of the 2026-08-13 signature-level audit and repairs; gate status
  now lives in the arc plan's crosswalk.

## Technical support

- [`ARCHITECTURE.md`](ARCHITECTURE.md) — layer map of the ~113 Lean modules.
- [`OVERVIEW.md`](OVERVIEW.md) — informal physicist-facing summary, bounded
  by the ledger.
- [`METHODOLOGY.md`](METHODOLOGY.md) — the audit-gated development process.
- [`GENERIC_RECONSTRUCTION.md`](GENERIC_RECONSTRUCTION.md) — algebraic scalar
  and Ricci entrance machinery.
- [`PHASE_III_MAXWELL_RECONSTRUCTION.md`](PHASE_III_MAXWELL_RECONSTRUCTION.md)
  — Maxwell reconstruction interfaces.
- [`PHASE_IV_UPLIFT.md`](PHASE_IV_UPLIFT.md) and
  [`UPLIFT_CONVENTION.md`](UPLIFT_CONVENTION.md) — conditional Kaluza uplift
  layer.

## Archive

Historical snapshots and redirects live in [`archive/`](archive/):
`RESEARCH_STATE`, `RESEARCH_RESET`, `HIGH_IMPACT_PROGRAM`,
`PROGRAM_SYNTHESIS`, `REALIGNED_EXECUTION_PLAN`, `RELEASE_CHECKLIST`,
`VIBEMATHED_POSITIONING`, legacy `NOTATION`, and the draft `RELEASE_NOTES`.
The superseded first paper track is in
[`../papers/archive/paper-01/`](../papers/archive/paper-01/).  None of these
are sources of current claims, priorities, or submission wording.

## Precedence

When documents disagree, use this order:

1. `CLAIM_LEDGER.md` for what may be claimed;
2. the active manuscript for exposition;
3. `RESEARCH_PLAN.md` for what to do next on the paper, and
   `KALUZA_ARC_PLAN.md` for post-paper sequencing.
