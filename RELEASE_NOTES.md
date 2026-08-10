# Draft release notes

## v0.2.0 — Generic pointwise reconstruction orbit

This release is the proposed primary source for a VibeMathed partial-result
submission once it has a public pinned GitHub URL.

### Principal result

For the generic complementary spectral block of the convention-fixed
`a=√3` Einstein--Maxwell--dilaton Ricci endomorphism, the release proves:

- the coordinate-free rank-one scalar square law;
- the noncommutative Sylvester reconstruction equation;
- exact forced diagonal and Lorentz-sign existence conditions;
- scalar-factor uniqueness for a fixed block up to global sign;
- classification of all scalar-generated solutions into one of two
  relative-sign-related tensors;
- distinctness of those tensors on the genuine two-component branch;
- invariance of the Ricci data under the spectral reflection exchanging them;
- a basis-independent construction of that reflection from an idempotent
  spectral projector.

The result is a pointwise existence-and-orbit classification and a no-go
theorem for curvature-only uniqueness. It is not a local EMD geometrization or
Kaluza uplift theorem.

### Verification

Run `bash scripts/audit.sh`. The release is required to build with warnings
treated as errors, contain no `sorry`, `admit`, or project axioms, and print the
axiom dependencies of every advertised theorem.

### Public release placeholders

- Git tag: `v0.2.0`
- Commit: `[PIN AFTER FINAL AUDIT]`
- Passing workflow: `[PIN AFTER PUBLIC PUSH]`
- Independent statement/domain audit: pending

