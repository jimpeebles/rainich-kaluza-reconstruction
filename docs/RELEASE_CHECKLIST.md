# Historical public-release checklist (superseded)

> This checklist records the repository's earlier centralizer-only release
> boundary. It is not the policy for the current coupling-detector paper.
> Use [`RESEARCH_PLAN.md`](RESEARCH_PLAN.md),
> [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md), and
> [`../papers/coupling-detector/MANUSCRIPT.md`](../papers/coupling-detector/MANUSCRIPT.md)
> for current claims. In particular, differential coupling recovery is now
> proved on the explicit active regular locus, while a converse and full
> nonlinear-coordinate covariance remain open.

The first public release is intended to support a VibeMathed **partial result**,
not a claim that generalized Rainich--Kaluza reconstruction is solved.

## Mathematical release boundary

- [x] Fix one `a=√3` EMD action and derive `𝓡=S+V` and `tr(V)=R`.
- [x] Prove the rank-one square law without choosing a basis.
- [x] Derive the noncommutative reconstruction equation.
- [x] Classify generic complementary scalar blocks and their signature test.
- [x] Classify factorization of a fixed block up to global scalar sign.
- [x] Exhibit and classify the distinct relative-sign tensor ambiguity.
- [x] Prove that spectral reflection preserves Ricci data and exchanges the two
  scalar tensors.
- [ ] Obtain an independent domain review of the EMD normalization and novelty
  boundary.
- [x] Construct the Ricci-centralizing involution basis-independently from an
  idempotent spectral projector.

## Artifact requirements

- [ ] Replace provisional author metadata only after the collaborators approve
  the public attribution.
- [ ] Create a public GitHub repository.
- [ ] Enable the included GitHub Actions workflow and record a passing run.
- [ ] Tag a pinned release and attach or link the manuscript.
- [ ] Confirm a clean clone passes `bash scripts/audit.sh`.
- [ ] Include the release URL, repository URL, and passing workflow URL in the
  VibeMathed submission.
- [ ] Preserve the exact AI-contribution disclosure in the release.

## Allowed release claim

The release may claim a machine-checked generic pointwise classification and a
discrete centralizer obstruction to curvature-only uniqueness.

It must not claim a local EMD geometrization theorem, differential
reconstruction, or five-dimensional uplift criterion.
