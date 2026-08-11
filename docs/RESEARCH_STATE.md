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

Phase III has reached its generic local decision interface. For `S=𝓡-V`, the reconstruction equation is
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
separated by the chosen probes. The candidate recovered from those probes is
now validated by exact local exterior obstruction forms.

The canonical square-root clause itself is no longer merely schematic. Lean
now represents `𝓕=Ee⁰∧e¹+Be²∧e³` as an explicit antisymmetric `4×4` tensor,
raises indices with the `(-,+,+,+)` metric, and evaluates the Maxwell stress
definition component by component. It obtains the tracefree
`diag(-ρ,-ρ,ρ,ρ)` form, square law, nonnegative energy density, Hodge action,
and duality invariance. Every `q>0` canonical residual has the explicit real
seed `E=√(2q),B=0`. Its local transport and patching algebra is now complete
on a fixed-probe principal-frame patch.

The coordinate dependence of that calculation has now also been removed at
the finite-dimensional level. For any supplied Lorentz frame and inverse,
Lean proves that congruence transport preserves antisymmetry and carries the
matrix Maxwell stress by similarity. The square identity and complementary
principal-projector splitting transport with it, and the positive-`q` seed
realizes the transported residual. The following fixed-probe construction
produces the required local Lorentz frames explicitly.

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
evaluated first-jet connection and exterior-form assembly are now complete in
that local trivialization.

For the Maxwell seed overlaps, the transition algebra is now verified beyond
the constant case. Unit duality parameters have an associative composition,
identity, inverse, and action cocycle. Applying the product rule to a variable
transition of rate `τ` gives the exact Lean-checked law `ω↦ω+τ`. A local
connection coefficient transforming as `A↦A+τ` therefore makes `ω-A`
overlap-invariant. The evaluated two-channel reconstruction obeys the same
law, while its recovered EMD coupling is invariant. This supplies the local
overlap law; global transition topology is not part of the generic local
claim.

At the exterior-algebra level, the duality product rule and both EMD closure
equations are now formalized with one-, two-, and three-form types. The exact
seed-channel iff exposes a new generic orbit result: nonzero dilaton coupling
with an active source channel breaks constant duality from a circle to the
overall sign. Lean also verifies the complementary exceptional cases: the
full circle survives at zero coupling or when both scalar-source wedge
channels vanish.

The transported seed has now also been differentiated explicitly. With
`Ω=(dL)L⁻¹`, Lean separates the derivative into the amplitude term
`(dq/2q)𝓕can` and the Lorentz-frame terms
`Ωᵀ𝓕can+𝓕canΩ`, and proves that the differentiated Lorentz constraint puts
`Ω` in the Lorentz Lie algebra. Exteriorizing four such directional
derivatives produces alternating seed and Hodge-seed three-forms. Two explicit
obstruction forms vanish if and only if the full local EMD closure equations
hold. Together with channel recovery and the constant-orbit theorem, this
completes the conditional generic local Phase-III output: either a certified
empty list or the accepted `(v,𝓕,a)` orbit, with only overall sign on the
active nonzero-coupling locus.

The local scalar and weighting handoff is now in place as well. For actual
differentiable one-form fields on an open convex patch, Lean proves the
relative-sign closure theorem and integrates the unique generic closed branch
to `v=dφ` using Mathlib's Poincare lemma. The potential is unique up to an
additive constant. Lean differentiates `exp(∓aφ/2)` and proves directly that
accepted Phase-III data give a closed physical Maxwell two-form and a closed
weighted Hodge flux. The orientation-independent condition `a²=3` always
permits one scalar orientation with `a=√3`. Phase IV now has a constructive
radial homotopy operator for the two-form. Lean proves radial gauge and proves,
from the cyclic closedness identity and the fundamental theorem of calculus,
that the integrated derivative candidate has curvature exactly `F`. A
specialization of Mathlib's dominated parametric-integral theorem records the
honest analytic conditions needed to identify that candidate with the
derivative of the potential. Lean also verifies the pointwise gauge-jet orbit,
proves the field-level local relation `A'-A=dχ` and uniqueness of `χ` up to a
constant, and proves invariance of `dz+cA` and the warped Kaluza metric under
the compensating fifth-coordinate shift. The full bilinear block is also
proved symmetric and nondegenerate under the expected base hypotheses. The
Phase-IV.1 splice is now discharged: the `C¹` closed regularity package on a
star-shaped patch proves the radial potential Frechet differentiable with
`dA=F`, uniformly in every evaluation direction, closing the generic local
two-form Poincare theorem with potential orbit `A+dχ`. The IV.2 uplift
constants `c₁=-1/√3, c₂=2/√3, c₃=1` are derived from the five-dimensional
Einstein-Hilbert action in `docs/UPLIFT_CONVENTION.md` and fixed as Lean
definitions whose three matching conditions are verified exactly, re-deriving
`a²=3` from the five-dimensional origin. The IV.3 coordinate layer now contains the
block-metric congruence assembly with explicit two-sided inverse formulas and
determinant `u⁴·v·det g`, the orthogonal-family signature lift, and the six
closed-form Christoffel blocks at a normal-gauge point, whose Maxwell shear
carries exactly the EMD weight `e^{√3φ}`. The second-jet layer is now
in place with a certified inverse-metric derivative, and all three Ricci
blocks are proved. `R̂₅₅` is the convention-fixed scalar equation,
`R̂_{n5}` is the weighted Maxwell equation, and `R̂_{np}` is the Einstein
residual plus the exact scalar trace correction. The opposite mixed block is
proved equal under commuting gauge second jets, so vanishing of the full
`5×5` Ricci tensor is Lean-proved equivalent, in both directions, to the
full normal-frame EMD system. The first smooth realization layer now extracts
these arrays from actual `C²` fields, proves their Schwarz symmetries, extends
the assembled metric circle-invariantly to a local product, and matches its
point value, first derivative, and complete second derivative to the
coordinate calculation. The remaining Phase-IV obligations are the intrinsic
Ricci identification and the IV.4 uniqueness/orbit classification. The first
of these has now been narrowed substantially: an ansatz-independent coordinate
Levi--Civita/Ricci layer is proved equal both to the Kaluza contraction and to
the curvature built from the actual local-product metric derivatives. The
arbitrary invertible affine coordinate-change case is now also complete:
Lean derives the transformed inverse jet, connection, differentiated
connection, and covariant Ricci law and proves that affine pullback both
preserves and reflects Ricci-flatness. No orthogonal or block-preserving
restriction is imposed, so the theorem includes affine changes mixing base
and circle directions. The genuinely nonlinear chart law, where the
connection has an inhomogeneous second-coordinate-derivative term, has now
been reduced to one metric realization identity. Lean derives the
inhomogeneous Christoffel law from the transformed metric first jet, certifies
the inverse-Jacobian derivative and product-rule differentiated connection,
and proves full nonlinear covariance and flatness equivalence for the
resulting connection Ricci contraction. Both the pure-coordinate and mixed
Hessian/old-connection cancellations are explicit theorems. The transformed
metric second jet is also constructed and its first-kind differentiated
connection law is verified. The metric endpoint now separately proves the
nonlinear product-rule derivative of the transformed inverse metric, the full
four-term differentiated first-kind pullback, and the undifferentiated raised
contraction into the inhomogeneous connection bracket. It remains to prove
the differentiated-bracket contraction assembling these identities into the
certified nonlinear differentiated connection. After that, the
coordinate-Ricci specialization and pseudo-Riemannian manifold packaging—not
the component curvature formula—remain.

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
