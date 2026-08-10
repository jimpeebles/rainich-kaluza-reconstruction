# VibeMathed submission draft

This is a staging document. Replace bracketed URLs and collaborator metadata
only when the public release exists.

| Field | Proposed value |
|---|---|
| Name | Pointwise Scalar Reconstruction and Its Discrete Ambiguity in Kaluza-Coupled EMD |
| Short name | Rainich--Kaluza scalar block |
| Result | Proved |
| Status | Partial result |
| Field | Mathematical physics |
| Field detail | Mathematical relativity; Rainich theory; Kaluza reduction |
| Solve date | 2026-08-10 |
| Source URL | `[PINNED RELEASE URL]` |
| Source name | Author repository release |
| AI contribution | AI-discovered |
| Model | OpenAI Codex (GPT-5 family) |
| Vendor | OpenAI |
| Verification | Lean-checked, statement unaudited |
| Publication | Announced, unless a preprint is posted first |
| Method | Argument |

## Statement

Separate Rainich-type results reconstruct Maxwell and scalar matter from
curvature, but the Kaluza-coupled Einstein--Maxwell--dilaton Ricci tensor
contains their sum. On the generic non-null branch, the coupled Sylvester
equation fixes the two scalar-block diagonal entries and yields exact
Lorentz-sign existence inequalities. Scalar factorizations of a fixed block
are unique up to global sign, but the curvature data admit two distinct scalar
tensors when both complementary components are nonzero. They are exchanged by
an involutive spectral reflection that commutes with the Ricci endomorphism.
The reflection is constructed basis-independently from the corresponding
idempotent spectral projector.

## Result qualifier

This resolves the generic pointwise complementary-block problem and proves a
discrete obstruction to curvature-only uniqueness. Spectral assembly on the
full tangent space, differential closure, Maxwell-field reconstruction, and a
local necessary-and-sufficient Kaluza uplift theorem remain open.

## What the AI did

Under human direction, OpenAI Codex identified the Sylvester reconstruction,
derived the signature-aware factorization conditions, detected the previously
overlooked relative-sign nonuniqueness, developed the centralizer/reflection
classification, wrote the Lean formalization and manuscript scaffolding, and
performed literature and adversarial-claim audits. The human collaborators
selected the research direction, reviewed the scope decisions, and retain
responsibility for the public claims.

## Verification note

The rank-one square law, noncommutative reconstruction equation, generic block
classification, Lorentzian existence criterion, global-sign factorization
uniqueness, relative-sign nonuniqueness, and spectral-reflection identities are
formalized in Lean 4 with pinned Mathlib. The repository contains no `sorry`,
`admit`, or project axioms; `lake build` and the advertised-theorem axiom audit
pass. The same AI system contributed to the statements and formal proofs, and
no independent domain expert has yet audited the informal-to-formal
correspondence, so the appropriate label is “Lean-checked, statement
unaudited.”

## More links

- Repository: `[PUBLIC REPOSITORY URL]`
- Passing Lean workflow: `[GITHUB ACTIONS RUN URL]`
- Manuscript or research announcement: `[PUBLIC DOCUMENT URL]`
