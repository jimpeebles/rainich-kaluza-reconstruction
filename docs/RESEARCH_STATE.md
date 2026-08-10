# Research state at repository creation

Date: 2026-08-10

## Primary project

The repository now centers the generalized Rainich–Kaluza reconstruction
problem. The scalar parametric-amplifier work is a possible downstream
application and is not evidence for the reconstruction theorem.

## Candidate generic algebraic structure

For the four-dimensional `a = √3` Einstein–Maxwell–dilaton equations, write the
mixed Ricci endomorphism schematically as

`R = S + V`,

where `S` is the scaled Maxwell stress endomorphism and
`V = ½ ∇φ ⊗ ∇φ` is rank one. For a non-null Maxwell field, Maxwell algebra gives
`S² = q² I`. The research conversations derived the candidate characteristic
factorization

`det(λI - R) = (λ² - q²)(λ² - R λ - c)`.

This implies:

- a protected opposite eigenvalue pair `±q`;
- `e₃ = -R q²` in the standard quartic sign convention;
- on `R ≠ 0`, `q² = -e₃/R`;
- the polynomial obstruction
  `C_KK = e₁²e₄ - e₁e₂e₃ + e₃² = 0`.

The Lean project verifies these coefficient consequences and the later generic
block results. It now also proves the basis-independent mechanism protecting
an eigenvalue under a rank-one perturbation whenever the original eigenspace
contains two linearly independent vectors. Applying this separately to the
two non-null Maxwell principal planes produces nonzero `+q` and `-q`
eigenvectors of the full Ricci endomorphism. The exterior-algebra proof that
the Maxwell eigenspaces have the required multiplicities remains open. Lean
now also proves the converse polynomial step: any monic quartic with nonzero
roots `+q` and `-q` necessarily factors by `x²-q²`, with the complementary
quadratic fixed by the first two characteristic coefficients. Thus the only
remaining bridge to the proposed characteristic factorization is the formal
four-dimensional passage from the Maxwell principal planes, through the
protected eigenvectors, to roots of the Ricci characteristic polynomial.

## Candidate reconstruction step

The proposed scalar-gradient tensor should satisfy

`R V + V R - R V = R² - q² I`,

where the unadorned scalar `R` on the left is the Ricci trace. A publishable
result requires proving existence and classifying the Ricci-centralizer orbit
of admissible rank-one solutions on a generic Lorentzian branch, then proving
which covector representatives are closed and hence locally scalar gradients.

After choosing a centralizer orbit representative for `V`, one sets `S = R - V`
and must impose the classical
algebraic and differential Maxwell–Rainich conditions. The scalar equation and
the electromagnetic duality-complexion ambiguity supply additional closure
conditions.

## New discrete obstruction

The pointwise algebra does not uniquely reconstruct `V` on the genuinely
two-component branch. Reversing one scalar component preserves both forced
diagonal entries and the Sylvester equation but changes both off-diagonal
entries. The two tensors are exchanged by reflection of one complementary
Ricci eigendirection. This reflection commutes with the Ricci block, so no
pointwise invariant built only from that curvature endomorphism can select
between them. The formal development classifies all scalar-generated block
solutions into these two possibilities.

At the first differential layer, write the two covector candidates as
`α+β` and `α-β` in the complementary spectral splitting. For any real-linear
differential operator `d`, Lean now proves that both branches lie in `ker d`
if and only if `dα=dβ=0`. Thus differential closure generically removes the
pointwise ambiguity; it fails to do so precisely on the separately closed
locus. This does not prove that either candidate is closed, nor does it yet
instantiate `d` as the exterior derivative on a Lorentzian manifold.

The differential-coupling layer now goes one step farther. For the rescaled
Maxwell equations `2d𝓕=a(v∧𝓕)` and
`2d(*𝓕)=-a(v∧*𝓕)`, Lean proves uniqueness of `a` on either nonzero channel,
orientation invariance of `a²`, and the Lorentzian-pairing formula for `a²`
when the source three-form is non-null. The primal and dual pairing formulas
are proved to agree. These are evaluated-channel theorems; obtaining the
forms from curvature is still open.

For smooth branch construction, the repository also proves that the
polynomial `Pₐ=(R-bI)/(a-b)` is the idempotent Ricci-commuting projector on a
two-root invariant block. This removes eigenvector orientation from the next
spectral-splitting step.

## Evidence inherited from earlier conversations

The candidate algebraic fingerprint was numerically reported to hold to
floating-point precision on a rotating dyonic Kaluza black-hole metric and
across a parameter scan. Those calculations are **unreproduced provenance
items** until their source, conventions, and data are recovered or independently
rebuilt in this repository.

Related work on spin-induced scalar multipoles and binary observables remains
interesting but is not part of Paper I unless it supplies an exact-solution
test of the reconstruction theorem.

## Important corrections retained from adversarial review

- Separate scalar and Maxwell geometrization results already exist.
- Higher-dimensional algebraic Rainich theory already exists.
- A characteristic-polynomial identity alone is neither unique to Kaluza
  gravity nor sufficient for reconstruction.
- Null fields, zero Ricci trace, repeated eigenvalues, and global duality data
  cannot be hidden inside a “generic” proof.
- Numerical agreement on known solutions is a unit test, not a novelty proof.

## Downstream amplifier track

The quadratic scalar/EM cavity model and its Lean Hamiltonian audit will be
preserved later under a separate application directory. It should reconnect to
this repository only if the relevant four-dimensional EFT coupling is derived
with matched conventions or explicitly declared independent of Kaluza theory.
