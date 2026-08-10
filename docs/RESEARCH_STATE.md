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
locus. Lean also proves the sharp existence-to-uniqueness statement: away
from that locus, if either branch is closed, exactly one branch is closed.
This does not prove that either candidate is closed, nor does it yet
instantiate `d` as the exterior derivative on a Lorentzian manifold.

The differential-coupling layer now goes one step farther. For the rescaled
Maxwell equations `2d𝓕=a(v∧𝓕)` and
`2d(*𝓕)=-a(v∧*𝓕)`, Lean proves uniqueness of `a` on either nonzero channel,
orientation invariance of `a²`, and the Lorentzian-pairing formula for `a²`
when the source three-form is non-null. The primal and dual pairing formulas
are proved to agree. These are evaluated-channel theorems; obtaining the
forms from curvature is still open.

For smooth branch construction, the repository proves the two-root polynomial
projector and the full four-root Lagrange resolution without choosing an
eigenbasis. At the differentiated-algebra level it further proves

`dPᵢ = Σ_{j≠i}(aᵢ-aⱼ)⁻¹[Pⱼ(dR)Pᵢ + Pᵢ(dR)Pⱼ]`.

Thus the full projector derivative is fixed by the Ricci derivative and
spectral gaps; eigenvalue derivatives cancel. The outstanding geometric step
is smooth Levi-Civita instantiation. The evaluated scalar-amplitude layer is
also now explicit: derivatives of `q²`, both forced scalar diagonals, and both
nonzero scalar amplitudes are rationally reconstructed from characteristic and
root derivatives. Combining these results into smooth one-form derivatives
and antisymmetrizing into `dα,dβ` remains open.

Phase III has now begun. For `S=𝓡-V`, the reconstruction equation is
Lean-verified to be equivalent to `S²=q²I` once the scalar square law is
imposed, and matching traces make `S` tracefree. On the non-null branch,
`S/q` yields two orthogonal polynomial projectors `½(I±S/q)` resolving the
Maxwell principal subspaces.

At the canonical principal-frame level, the non-null square roots are now
Lean-classified exactly: equal nonzero `E²+B²` amplitudes form one duality
circle, and the unit parameter between any two representatives is constructive
and unique. Its derivative contains exactly one complexion rate. Moreover, a
two-probe system with determinant `Δ=z₁y₂-z₂y₁≠0` uniquely recovers that rate
and the signed EMD coupling simultaneously. This exposes a new explicit
degenerate locus `Δ=0` where those two differential responses cannot be
separated by the chosen probes. The remaining obligations are smooth
exterior-form assembly, differential closure, and construction of the probe
data from exterior derivatives.

The canonical square-root clause itself is no longer merely schematic. Lean
now represents `𝓕=Ee⁰∧e¹+Be²∧e³` as an explicit antisymmetric `4×4` tensor,
raises indices with the `(-,+,+,+)` metric, and evaluates the Maxwell stress
definition component by component. It obtains the tracefree
`diag(-ρ,-ρ,ρ,ρ)` form, square law, nonnegative energy density, Hodge action,
and duality invariance. Every `q>0` canonical residual has the explicit real
seed `E=√(2q),B=0`. The remaining geometric issue is transporting and patching
this canonical construction over smooth oriented principal-plane bundles—not
existence of a canonical algebraic square root.

The coordinate dependence of that calculation has now also been removed at
the finite-dimensional level. For any supplied Lorentz frame and inverse,
Lean proves that congruence transport preserves antisymmetry and carries the
matrix Maxwell stress by similarity. The square identity and complementary
principal-projector splitting transport with it, and the positive-`q` seed
realizes the transported residual. What remains is no longer a frame-algebra
calculation: it is the smooth bundle theorem producing local oriented Lorentz
frames from the projector fields and describing their transition functions.

An explicit principal-frame construction has now reduced that theorem further.
Lean verifies Lorentzian and spacelike two-plane Gram--Schmidt, proves that the
normalized vectors remain in their curvature-polynomial projector ranges, and
proves all cross-plane inner products vanish. Four ambient probe vectors with
strict projected Gram-sign conditions therefore generate a full
pseudo-orthonormal tetrad by an explicit formula. The Maxwell projectors are
verified to satisfy the necessary idempotence, annihilation, and metric
self-adjointness hypotheses. The pointwise existence issue is now resolved as
well. In four dimensions the tracefree involution forces both projector ranges
to have rank two; index-one Lorentz signature and a timelike witness in the
physical minus range then produce suitable noncollinear probes, a
pseudo-orthonormal tetrad basis, and a real skew two-form whose Maxwell stress
is exactly the supplied residual. The
strict Gram signs are Lean-verified to persist on a neighborhood whenever
their scalar functions are continuous. On such a patch, Lean now proves that
the fixed-probe tetrad, its matrix, and the transported positive-`q` seed are
`C^n`. Its transpose is a Lorentz coframe, `K=G LᵀG` is a smooth two-sided
inverse, and the seed has the transported residual as its Maxwell stress. The
remaining geometric connector is intrinsic bundle orientation/connection and
exterior-form assembly.

For the Maxwell seed overlaps, the transition algebra is now verified beyond
the constant case. Unit duality parameters have an associative composition,
identity, inverse, and action cocycle. Applying the product rule to a variable
transition of rate `τ` gives the exact Lean-checked law `ω↦ω+τ`. A local
connection coefficient transforming as `A↦A+τ` therefore makes `ω-A`
overlap-invariant. The evaluated two-channel reconstruction obeys the same
law, while its recovered EMD coupling is invariant. The remaining problem is
to instantiate this algebra with smooth transition maps, connection one-forms,
and curvature-derived exterior-form channels on the principal-plane bundles.

At the exterior-algebra level, the duality product rule and both EMD closure
equations are now formalized with one-, two-, and three-form types. The exact
seed-channel iff exposes a new generic orbit result: nonzero dilaton coupling
with an active source channel breaks constant duality from a circle to the
overall sign. Lean also verifies the complementary exceptional cases: the
full circle survives at zero coupling or when both scalar-source wedge
channels vanish.

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
