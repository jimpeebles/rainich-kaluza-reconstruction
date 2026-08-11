# Research roadmap

The high-impact theorem program and its phase exit criteria are specified in
[`docs/HIGH_IMPACT_PROGRAM.md`](docs/HIGH_IMPACT_PROGRAM.md). This roadmap
tracks the same program at repository-task granularity.

## Phase 0 — Provenance and novelty audit

- Fix the exact `a = √3` EMD action, frame, signature, and normalizations.
- Re-derive the Einstein, Maxwell, and scalar equations.
- Build a specialist bibliography for coupled Rainich/EMD inverse problems.
- Recover or independently reproduce all inherited numerical calculations.

Exit criterion: every starting equation has a source or derivation and every
novelty statement is phrased comparatively.

## Phase 1 — Generic algebraic reconstruction

- Derive the Ricci characteristic factorization from `R = S + V`.
- Prove that rank-one scalar perturbations retain one direction in each
  two-dimensional Maxwell principal plane. **Complete in Lean.**
- Formalize the four-dimensional Maxwell principal-plane multiplicities and
  convert the protected eigenvectors into characteristic-polynomial factors.
- Prove that nonzero opposite roots force the complete quadratic
  characteristic factorization. **Complete in Lean.**
- Formalize the rank-one determinant identity in Lean.
- Prove the protected eigenpair and invariant formulas.
- Solve the linear tensor equation for `V` on the generic branch.
- Prove admissibility and factorization uniqueness for a fixed tensor up to the
  scalar global sign.
- Classify the additional relative-sign tensor ambiguity and its Ricci
  centralizer action.
- Construct counterexamples to algebraic sufficiency.

Exit criterion: a zero-placeholder theorem package for the generic algebraic
step, including an honest existence/orbit classification and every
nondegeneracy hypothesis.

## Phase 2 — Differential closure and local sufficiency

- Factor the reconstructed rank-one tensor into a covector up to sign.
- Determine which differential conditions select or identify the two
  pointwise relative-sign partners.
- Prove that both relative-sign branches can be closed only on the locus where
  their two spectral components are separately closed. **Complete in Lean as
  an abstract linear differential lemma.**
- Prove that away from the separately closed exceptional locus, existence of
  a closed relative-sign branch makes that branch unique. **Complete in Lean
  as an abstract linear differential theorem; geometric existence remains
  open.**
- State and prove the closure condition implying local exactness. **Complete
  on open convex coordinate patches using Mathlib's one-form Poincare lemma;
  the potential is unique up to an additive constant.**
- Apply Maxwell–Rainich algebraic and differential conditions to `S = R - V`.
- Add the Kaluza scalar equation and duality-complexion datum.
- Derive the rescaled Maxwell differential channels and prove abstract
  uniqueness of `a` on a nonzero channel. **Complete in Lean at the evaluated
  module level; curvature and differential-form instantiation open.**
- Construct an intrinsic `a_geom²` and test `a_geom²=3` on Kaluza metrics and
  `a_geom²≠3` on adversarial EMD metrics.
- Prove the Lorentzian-pairing formula for `a_geom²` and primal/dual channel
  agreement. **Complete in Lean on the non-null evaluated-channel branch.**
- Construct the two-root polynomial spectral projector without eigenvectors.
  **Complete in Lean.**
- Construct the full four-root Lagrange projectors, prove their action,
  idempotence, Ricci commutation, and resolution of the identity without a
  chosen eigenbasis. **Complete in Lean under an explicit simple-spectrum
  decomposition hypothesis; smooth tensor-field promotion and differentiation
  remain open.**
- Differentiate the full projector formula on the constant-gap branch and
  express `∇Pᵢ` using `R`, `∇R`, and derivatives of the four curvature roots.
  **The complete four-block formula, its universal off-diagonal identities,
  and vanishing target block are complete in Lean; eigenvalue derivatives
  cancel. Smooth-bundle instantiation remains open.**
- Differentiate the scalar amplitudes, combine them with `∇Pᵢ`, and
  antisymmetrize to obtain curvature-derived formulas for `dα` and `dβ`.
  **Amplitude and `q²` derivative formulas are complete in Lean at the
  evaluated algebraic level; smooth assembly and antisymmetrization remain.**
- Prove that every accepted scalar candidate leaves a tracefree residual
  obeying the Maxwell square identity. **Complete in Lean under the explicit
  scalar square and trace hypotheses.**
- Normalize the non-null Maxwell residual and reconstruct its two principal
  projectors without eigenvectors. **Complete in Lean; the real two-form
  square root and complexion reconstruction are completed below.**
- Classify the non-null canonical Maxwell square roots as a duality orbit.
  **Complete in Lean at the principal-frame amplitude level, including a
  constructive and unique duality parameter; the geometric local lift is
  completed below.**
- Differentiate the duality orbit and solve simultaneously for the complexion
  rate and EMD coupling. **Unique unit-circle rate and nondegenerate two-probe
  recovery are complete in Lean; exterior-form channel identification and
  full obstruction validation are completed below.**
- Realize the canonical amplitudes as a Lorentzian two-form and verify its
  stress tensor, Rainich square, energy sign, Hodge action, and positive-`q`
  seed. **Complete in Lean in an explicit orthonormal frame, with smooth local
  transport and patching completed below.**
- Prove Lorentz-frame covariance of the two-form seed, Maxwell stress, square
  law, and principal projectors. **Complete in Lean for supplied mutually
  inverse Lorentz matrices; smooth local-frame construction and local overlap
  algebra are completed below.**
- Construct principal-plane frames from the curvature-polynomial projectors.
  **Explicit Lorentzian/spacelike Gram--Schmidt, projector-range preservation,
  cross-plane orthogonality, and the projected-probe pseudo-orthonormal tetrad
  criterion are complete in Lean. In dimension four, trace of the normalized
  involution now forces both ranges to have rank two; index-one signature and
  a timelike witness in the physical minus range yield suitable probes, a
  principal tetrad basis, and a real skew two-form whose Maxwell stress is
  exactly the residual. Strict Gram signs persist locally for continuous data.
  The fixed-probe tetrad, frame matrix, and transported seed are now proved
  `C^n` on each strict sign patch. The Lorentz coframe, explicit smooth
  inverse, transported stress equality, evaluated connection, and local
  exterior-form assembly are also complete.**
- Formalize local-seed overlap transitions and complexion patching. **The
  duality group law, inverse, cocycle, and full variable-transition rate law
  `ω↦ω+τ` are complete in Lean. The corrected quantity `ω-A` and the recovered
  coupling are overlap invariant when `A↦A+τ`; this supplies the local
  transition law, while global bundle topology is deferred.**
- Substitute the duality rotation into the exterior equations. **The exact
  `±ω∧` product-rule terms and an iff reduction to two seed-channel equations
  are complete in Lean. For nonzero coupling with an active scalar-source
  channel, constant duality freedom collapses to overall sign; the full circle
  survives precisely on the proved zero-coupling/inactive-source exceptional
  loci. The transported seed/Hodge-seed first jets now exteriorize to explicit
  alternating three-forms.**
- Prove a local necessary-and-sufficient theorem. **Complete on the generic
  local branch: two explicit obstruction three-forms vanish iff the EMD
  equations close, and the accepted constant orbit is classified.**
- Build the Phase-IV handoff. **Complete conditionally on the accepted scalar
  branch: the unique closed relative-sign branch has a local scalar potential,
  the exponential unweighting derivatives are exact, the physical Maxwell
  field and weighted dual flux are closed, and `a²=3` can be oriented to
  `a=√3`. Phase IV now defines the radial gauge potential, proves its radial
  gauge condition, verifies the closedness-to-curvature fundamental-calculus
  identity for its derivative candidate, and proves Kaluza gauge invariance.
  The IV.1 splice is complete: under a `C¹` closed regularity package on a
  star-shaped patch, the dominated differentiation hypotheses are discharged
  uniformly and the radial potential satisfies `dA=F`, with the local
  potential orbit exactly `A+dχ`. The IV.2 convention constants
  `c₁=-1/√3, c₂=2/√3, c₃=1` are derived in `docs/UPLIFT_CONVENTION.md` and
  fixed as verified Lean definitions. The IV.3 coordinate layer is complete:
  block-metric congruence assembly, explicit inverse formulas, determinant
  and signature lift, and the six closed-form Christoffel blocks at a
  normal-gauge point are complete in Lean, together with the second-jet layer
  and all three Ricci blocks. The fiber block is the scalar equation, the
  mixed block is the weighted Maxwell equation, and the base block is the
  Einstein residual plus its exact scalar trace correction. Mixed-order
  symmetry is certified for genuine second jets, and vanishing of the full
  `5×5` Ricci tensor is Lean-proved equivalent to the complete normal-frame EMD
  system. The smooth local-product/normal-coordinate wrapper is next.**

Exit criterion: Paper I candidate with manuscript-to-Lean claim translation.

## Phase 3 — Degenerate branches

Treat `R = 0`, null Maxwell fields, null scalar gradients, `q = 0`, repeated
eigenvalues, and eigenvalue collisions separately. Determine whether each has
a reconstruction theorem, a no-go theorem, or unavoidable nonuniqueness.

## Phase 4 — Exact and adversarial metrics

- Validate on several exact Kaluza/EMD solutions.
- Test non-Kaluza scalar, electrovacuum, perfect-fluid, and mixed-matter metrics.
- Distinguish algebraic false positives from differential false positives.
- Use exact arithmetic or certified residual bounds where possible.

## Phase 5 — Applications

Only after the reconstruction theorem is stable should the project reconnect
to spin-induced scalar multipoles, binary signatures, or the scalar parametric
amplifier. Each application must state whether it follows from Kaluza reduction
or from an independent EFT assumption.
