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
contains two linearly independent vectors. The formerly open principal-plane
seam is now closed without a separate exterior-algebra multiplicity theorem:
in dimension four, trace zero and `S²=q²I` with `q≠0` force both polynomial
projector ranges to have rank two. Lean extracts independent pairs, proves
they are `±q` eigenvectors of `S`, protects one of each under the scalar
rank-one perturbation, and converts them to roots of the actual Mathlib
characteristic polynomial. The canonical coefficient extraction then gives
the complete `(x²-q²)` factorization, the necessary obstruction `C_KK=0`, and
recovery of the actual `q²` when the Ricci trace is nonzero. The Maxwell square
law itself remains the named four-dimensional algebraic input.

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
This does not prove that either candidate is closed. The coordinate-local
exterior instantiation is now supplied by `CurvatureScalarBranchJet4`; what is
still missing is a theorem forcing one of its two explicit obstruction
matrices to vanish.

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
spectral gaps; eigenvalue derivatives cancel. The coordinate-local geometric
instantiation is now complete. The Lagrange matrices are `C^n` wherever their
three labeled gaps stay nonzero; fixed projected probes and strict-sign
normalization give smooth metric-dual eigen-one-forms. Ordinary coordinate
product rules are proved to become the corresponding mixed-tensor
Levi--Civita identities, yielding the same four-block formula for `∇Pᵢ`.
The fixed-probe fields themselves are now differentiated explicitly: the
matrix action, metric contraction, reciprocal square-root scale, normalized
vector, and metric dual give exact timelike/spacelike Frechet formulas and
their actual coordinate jets.
The evaluated scalar-amplitude formulas are assembled directionwise into
one-forms, and `CurvatureScalarBranchJet4` now supplies explicit
product-rule `dα,dβ` and branch obstructions `dα±dβ`.

The logical branch decision itself is now exact and exhaustive. Lean proves
that plus only, minus only, both, and neither correspond respectively to
`dα=-dβ≠0`, `dα=dβ≠0`, `dα=dβ=0`, and `dα≠±dβ`. The patch version permits
separate finite witnesses for the two failures and therefore returns a sharp
no-branch certificate without a universal existence assumption. The intended
recognition theorem need not force a preferred case: returning the complete
surviving list or a sharp empty-list obstruction is the correct output.

The classifier is now connected to actual local analysis.
`CurvatureBranchIntegration.lean` represents the coordinate one-forms as
continuous linear maps and proves that the displayed exterior matrix vanishes
exactly when the corresponding genuine field is closed, provided the
displayed jet is its actual Frechet derivative. On an open convex patch this
is equivalent to local scalar-potential existence. Hence the plus-only,
minus-only, both, and neither cases give an exact exhaustive one/one/two/zero
potential classification, and the two finite witnesses prohibit either
potential. The derived realization is now automatic at the constituent-field
level. Coordinate-basis components reconstruct scalar and one-form Frechet
derivatives in arbitrary directions; the product rule then proves that the
full `xθ` derivative is exactly the displayed spectral-component jet.
`CurvatureScalarBranchComponentPatch4.ofCoordinateFDerivs` packages this into
the realized classifier without assuming the product rule, and
`ofFixedProbeCurvatureEigenCovectors` now inserts the actual normalized
timelike/spacelike eigen-one-form jets. Exact quotient and square-root
differentiation now identifies both reconstructed scalar-amplitude coordinate
jets as well, and `ofConcreteFixedProbeCurvatureFields` constructs the full
component patch without derivative-identity inputs. Every surviving branch
therefore goes directly to the Phase-III obstruction interface.
HC1 is downstream of this scalar integration decision.

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
coordinate calculation. An ansatz-independent coordinate Levi--Civita/Ricci
layer is proved equal both to the Kaluza contraction and to
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
contraction into the inhomogeneous connection bracket. The affine and
inhomogeneous differentiated raising contractions are now proved separately
and assembled into the certified nonlinear Christoffel jet. Unconditional
coordinate-Ricci covariance, two-sided Ricci-flatness, and the nonlinear
Kaluza specialization follow. The remaining coordinate-independence seam is
now closed at the intended local level in `IntrinsicKaluzaLocal.lean`. A
symmetric nondegenerate coordinate two-jet is extracted from the actual
componentwise `C²` Kaluza metric on the circle-invariant product patch, the
normal frame displays signature `(-,+,+,+,+)`, and finite-jet overlap
covariance proves pairwise chart independence. The resulting intrinsic local
Ricci-flatness predicate is equivalent to EMD. This does not claim a global
circle quotient or global pseudo-Riemannian manifold topology. The remaining
local presentation freedom is now also classified in
`KaluzaUpliftOrbit.lean`. Within the product-preserving circle-coordinate
class, equivalence of two Kaluza block metrics is iff the warped-base,
fiber-radius, and connection compatibility laws. Exact local gauge shifts,
dilaton/radius rescaling, and sign/fiber reversal are instances. The active
duality orbit is exactly overall sign, while zero coupling and inactive
source channels retain the exceptional circle. The conditional uplift module
is now assembled in `ConditionalKaluzaUplift.lean`. Its accepted-branch
certificate makes the abstraction seam explicit: a scalar point
normalization, post-unweighting `C¹` Maxwell closure, and a normal-gauge
realizer are required. The theorem then integrates and normalizes the scalar,
chooses the radial Maxwell potential, constructs the
intrinsically Ricci-flat Lorentzian product germ, retains the converse EMD
reduction, and returns all scalar, gauge, coupling, and presentation orbits.
`PhysicalMaxwellFieldRealization.lean` now fills the analytic Maxwell portion
of that certificate. It converts coordinate first jets to actual
continuous-bilinear Frechet derivatives, upgrades coordinate exterior
closure to arbitrary-direction cyclic closure, and proves that an accepted
branch with an actual matching rescaled first-jet realization yields the
exact closed `C¹` unweighted physical field. It now also carries the second
Phase-III channel through the same analytic layer, producing the genuine
closed positively weighted rotated Hodge flux instead of dropping it at the
completion boundary. The remaining official Phase-IV obligation is upstream.
`PhaseIIIRescaledSeedRealization.lean` further proves
that the rescaled realization follows from the two explicit componentwise
transported-seed derivative identities for the actual smooth `L,q` fields,
their jet continuity, and the actual complexion derivatives; the full
duality product rule and arbitrary-direction derivative reconstruction are
automatic. `CurvatureScalarContribution.lean` now constructs the actual
selected scalar mixed tensor `V=(1/2)v^sharp tensor v` from the inverse metric,
proves its rank-one trace square law and smoothness, and derives both its
metric self-adjointness and residual self-adjointness from certified metric
inverse identities. In the generic canonical Ricci frame it also proves the
full reconstruction equation from the two scalar amplitude identities and
then transports that equation through an arbitrary certified frame. The open
curvature seam is consequently the identification of the actual mixed
Ricci/scalar fields with that transported canonical pair and the
complexion/metric-Hodge identification, followed by the compatible
normal-gauge `C²` EMD realizer or a sharp obstruction.

## Exact validation infrastructure

Canonical Phase V has begun without advancing the Phase-IV gate. The pinned
`validation/` environment implements transparent coordinate formulas for the
Christoffel symbols, Ricci tensor, exterior derivative, convention-fixed EMD
residuals, and five-dimensional Kaluza uplift using exact SymPy expressions.
Every artifact records source provenance, canonical inputs, an expected
classification, runtime versions, and component-residual hashes; the audit
rejects byte-level drift.

The seed oracle uses flat four-dimensional spacetime in cylindrical
coordinates and the nonzero pure-gauge potential `A=d(r y)`. Its Kaluza metric
is proved computationally equal componentwise to the coordinate pullback
under `z' = z+r y`; both charts have nonzero Christoffel symbols while the
four- and five-dimensional Ricci tensors and all EMD residuals vanish. These
eight checks validate the harness contract and gauge-coordinate convention,
not the generic reconstruction theorem.

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
