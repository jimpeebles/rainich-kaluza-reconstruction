# Pointwise Scalar Reconstruction and Its Discrete Ambiguity in the Generic Kaluza Einstein--Maxwell--Dilaton Sector

## Abstract

Rainich theory asks when matter fields can be recovered from spacetime
curvature. Scalar and Maxwell fields have separate reconstruction theories,
but Kaluza reduction couples them in the four-dimensional
Einstein--Maxwell--dilaton (EMD) Ricci tensor. We isolate the generic pointwise
algebraic problem at Kaluza coupling `a=√3`. From the convention-fixed EMD
Einstein equation, the mixed Ricci endomorphism decomposes as `𝓡=S+V`, where
the Maxwell part satisfies `S²=q²I` and the scalar part is rank one with
`V²=tr(V)V`. We derive the noncommutative Sylvester equation

`𝓡V+V𝓡-tr(V)V=𝓡²-q²I`.

For a real diagonalizable generic branch with spectrum `{q,-q,a,b}`, `a≠b`,
we classify all scalar-generated solutions on the complementary eigenspace.
The diagonal entries are forced, their trace compatibility is automatic, and
real Lorentzian factorization is equivalent to two explicit
signature-adjusted inequalities. Factorization of a fixed tensor is unique up
to the global scalar sign. Nevertheless the curvature data do not determine a
unique scalar tensor: when both complementary components are nonzero there are
exactly two reflection-related tensors. The reflection commutes with the Ricci
endomorphism and can be constructed basis-independently from a spectral
idempotent. Thus pointwise curvature determines a centralizer orbit, not a
unique scalar contribution. The algebraic spine is formalized in Lean 4 with
no placeholders or project axioms. Differential closure and a full local
Rainich--Kaluza theorem remain open.

## 1. The coupled inverse problem

Classical Rainich theory characterizes an Einstein--Maxwell geometry directly
through curvature. Separate geometrization results similarly recover scalar
matter from a metric. In Kaluza theory these two matter sectors are not given
separately: the Ricci tensor records their sum. The pointwise question studied
here is therefore:

> Given the mixed Ricci endomorphism on the generic non-null Kaluza-coupled EMD
> branch, when does its complementary spectral block admit a real Lorentzian
> rank-one scalar contribution, and to what extent is that contribution
> determined by curvature?

This is a partial problem inside the larger local reconstruction question. It
does not ask whether the reconstructed covector is closed, whether the
residual stress has a Maxwell square root satisfying Maxwell's equations, or
whether the four-dimensional data uplift globally.

## 2. Convention-fixed EMD origin

We use Lorentz signature `(-,+,+,+)` and the action

`L = √(-g)[R - ¼e^(aφ)F² - ½(∂φ)²]`,

with `F=dA` and `a=√3`. This is the normalization used by Lü, Mao, and Wu for
the Kaluza reduction of five-dimensional vacuum gravity. The rearranged
Einstein equation is

`R_{μν}=½e^(aφ)(F_{μρ}F_ν{}^ρ-¼g_{μν}F²)+½∂_μφ∂_νφ`.       (2.1)

Define the mixed endomorphisms

`S^μ{}_ν=½e^(aφ)(F^{μρ}F_{νρ}-¼δ^μ{}_νF²)`,

`V^μ{}_ν=½v^μv_ν`, where `v=dφ`.

Then

`𝓡=S+V`, `tr(S)=0`, and `tr(V)=R=½v²`.                      (2.2)

The standard four-dimensional Maxwell--Rainich identity gives

`S²=q²I`,                                                  (2.3)

where

`q²=e^(2aφ)[(F²)²+(F·*F)²]/64`.

The scalar endomorphism is rank one, so basis-independently

`V²=tr(V)V`.                                               (2.4)

The Lean theorem `rankOneEndomorphism_sq_eq_trace_smul` proves (2.4) for every
finite free real module. Equation (2.3) is presently a named classical input,
not an exterior-algebra theorem formalized in this repository.

## 3. Coordinate-free reconstruction equation

No commutation between `S` and `V` is assumed. Expanding `𝓡=S+V` and using
(2.3)--(2.4) gives

`𝓡V+V𝓡-tr(V)V=𝓡²-q²I`.                                   (3.1)

This identity holds in every associative real algebra. It is verified by
`reconstructionEquation_of_decomposition`.

Equation (3.1) is equivariant under the Ricci centralizer. If `J²=I` and
`J𝓡=𝓡J`, then `V↦JVJ` maps solutions of (3.1) to solutions. This is verified
by `reconstructionEquation_conjugation_invariant`.

There is also a basis-independent reason for the protected pair in (4.1).
Let an eigenspace of `S` contain two linearly independent vectors and write
`V=x⊗f`. The restriction of `f` to that two-dimensional plane has a nonzero
kernel vector `y`. Hence `Vy=0` and

`𝓡y=(S+V)y=Sy=λy`.                                          (3.2)

The Lean theorem `exists_protected_eigenvector_of_pair` proves this over an
arbitrary real module. Its paired corollary
`exists_protected_opposite_eigenvectors` applies it to `+q` and `-q`
eigenplanes. The new four-dimensional assembly removes their multiplicities
as an extra input: trace zero and `S²=q²I`, `q≠0`, force both polynomial
projector ranges to have rank two. Theorems
`exists_maxwellResidual_principal_eigenpairs` and
`protected_opposite_isRoot_charpoly_of_maxwellResidual` then produce protected
nonzero `±q` vectors and prove that they are roots of the actual endomorphism
characteristic polynomial.

The remaining polynomial step is now exact. For a monic quartic in the sign
convention of Section 7, nonzero roots `+q` and `-q` force

`e₃=-e₁q²`, `e₄=-q²(e₂+q²)`,                           (3.3)

and hence

`p(x)=(x²-q²)(x²-e₁x+e₂+q²)`.                           (3.4)

This converse is verified by
`monicQuartic_factorization_of_opposite_roots` and
`characteristicData_eq_fromFactorization_of_opposite_roots`. The canonical
coefficient bridge and end-to-end statement are
`CharacteristicData.ofEndomorphism` and
`charpoly_factorization_of_maxwellResidual_add_rankOne_canonical`.
Consequently the proposed factorization is no longer an independent
coefficient ansatz on the stated square-law plus rank-one entrance package.

## 4. Generic complementary block

Assume that `𝓡` is real diagonalizable with eigenvalues

`{q,-q,a,b}`,                                               (4.1)

where `a≠b` and `tr(𝓡)=a+b=:T`. In an eigenbasis, (3.1) becomes

`(λ_i+λ_j-T)V^i{}_j=δ^i{}_j(λ_i²-q²)`.                    (4.2)

Away from additional eigenvalue-sum resonances, components involving the
protected `±q` eigendirections vanish. On the complementary `a,b` block, the
off-diagonal coefficient vanishes because `a+b=T`. The diagonal entries are
forced to be

`u=(a²-q²)/(a-b)`,

`w=(b²-q²)/(b-a)`.                                        (4.3)

Lean proves

`u+w=a+b`,                                                 (4.4)

and

`uw=-((a²-q²)(b²-q²))/(a-b)²`.                            (4.5)

Thus trace compatibility is automatic. A real symmetric rank-one completion
exists exactly when

`(a²-q²)(b²-q²)≤0`.                                       (4.6)

Theorem `solvesComplementaryBlock_iff` classifies every complementary
Sylvester solution; `exists_reconstructed_rankOne_completion_iff` proves
(4.6).

## 5. Lorentzian scalar factorization

Let `ε_a²=ε_b²=1` be the pseudo-orthonormal metric signs. Real covector
components `x,y` generate the mixed scalar block

`V^a{}_a=ε_a x²/2`, `V^b{}_b=ε_b y²/2`,

`V^a{}_b=ε_a xy/2`, `V^b{}_a=ε_b xy/2`.                  (5.1)

The forced diagonals (4.3) admit such a factorization if and only if

`ε_a u≥0` and `ε_b w≥0`.                                  (5.2)

In a definite-signature complementary block this refines (4.6); in general it
replaces it, and the two tests are incomparable on mixed-signature blocks.
Theorem
`exists_scalarComplementaryBlock_iff` proves that a scalar-generated block
solving all four complementary equations exists exactly under (5.2).
`scalarMixedBlock_metric_selfAdjoint` verifies symmetry after lowering the
raised index.

For a fixed nondegenerate block, its scalar components are unique up to
`(x,y)↦(-x,-y)`. This global sign changes the covector but not `V`; the statement
is verified by `scalarMixedBlock_components_unique_up_to_sign`.

## 6. Main algebraic result: two centralizer orbits

The preceding factorization uniqueness must not be confused with uniqueness
of `V` from curvature. Replace `y` by `-y` while keeping `x` fixed. The
diagonal entries in (5.1) are unchanged, while both off-diagonal entries change
sign. Since the complementary off-diagonal equations in (4.2) are resonant,
the new block is also a solution.

### Theorem 6.1 (two-branch classification)

On the generic branch `a≠b`, any two scalar-generated complementary solutions
are either equal or are related by the relative-sign flip

`(V^a{}_b,V^b{}_a)↦(-V^a{}_b,-V^b{}_a)`.                 (6.1)

If `x≠0` and `y≠0`, the two blocks are distinct.

This is verified by `scalarComplementarySolutions_eq_or_flip` and
`exists_distinct_relative_sign_solution`.

### Theorem 6.2 (spectral-reflection interpretation)

Let `J=diag(1,-1)` on the complementary eigenspace. Then

`J²=I`, `J diag(a,b)=diag(a,b)J`,                         (6.2)

and conjugation `V↦JVJ` realizes (6.1). Hence `J` preserves the Ricci data while
exchanging the two scalar tensors.

The matrix realization is verified by
`secondSpectralReflection_preserves_Ricci` and
`secondSpectralReflection_conjugates`.

The construction is intrinsic. If `P²=P` is the spectral projector onto the
second complementary eigenline, then

`J=I-2P`.                                                  (6.3)

Lean proves that (6.3) is involutive, commutes with every endomorphism
commuting with `P`, and acts on reconstruction solutions by conjugation. The
principal declaration is `reconstructionEquation_reflectionOfIdempotent`.

The projector need not be supplied abstractly. On a two-root invariant block
satisfying

`(𝓡-aI)(𝓡-bI)=0`, `a≠b`,

the polynomial

`Pₐ=(𝓡-bI)/(a-b)`                                         (6.4)

is idempotent, commutes with `𝓡`, acts as the identity on the `a` eigenspace,
and vanishes on the `b` eigenspace. These statements are verified by the
`twoRootProjector_*` theorem family. This supplies an eigenvector-free object
that can, after smooth geometric assembly, be differentiated in the local
closure problem.

The conclusion is a no-go statement: pointwise curvature algebra determines
the scalar tensor only up to the relevant Ricci-centralizer action. Additional
differential or orientation data are logically necessary for unique local
reconstruction.

### 6.3 First differential selection result

Write the two covector representatives in a smooth complementary spectral
splitting as

`v₊=α+β`, `v₋=α-β`.                                      (6.5)

Exterior differentiation is linear. Therefore

`dv₊=0` and `dv₋=0  ⇔  dα=0 and dβ=0`.                   (6.6)

The Lean theorem `both_relativeSign_branches_closed_iff` proves (6.6) for any
real-linear operator, so it applies to exterior differentiation once the
smooth differential-form setting has been supplied. Its corollary
`reflected_branch_closed_iff_of_branch_closed` says that, if one branch is
closed, the reflected branch is closed precisely on the separately closed
locus.

This does not establish that either candidate is closed. It does show that the
pointwise ambiguity is generically visible to first-order differential data:
both branches survive only under the stronger pair of conditions `dα=dβ=0`.

### 6.4 Smooth curvature-field realization

On a coordinate patch carrying four smooth labeled roots with nonvanishing
spectral gaps, define the four Lagrange projectors by the same cubic
polynomials in the mixed Ricci matrix. Lean now proves these matrix fields are
`C^n`, pointwise idempotent, and resolve the identity under the stated
four-eigenspace decomposition. Fixed probes, strict causal-sign normalization,
and metric duality then give smooth eigen-one-forms without choosing a moving
eigenbasis.

The mixed-tensor Levi--Civita derivative satisfies the connection product
rule. Therefore the coordinate derivatives of the projector and eigenvalue
equations imply

`∇Pᵢ=Σ_{j≠i}(aᵢ-aⱼ)⁻¹[Pⱼ(∇R)Pᵢ+Pᵢ(∇R)Pⱼ]`.             (6.7)

The scalar amplitude derivatives combine with the eigen-one-form jets by

`d(xθ)=dx∧θ+x dθ`.                                       (6.8)

The resulting `CurvatureScalarBranchJet4` has explicit obstruction matrices
`dα,dβ`, and Lean verifies that the exterior derivatives of the two candidates
are exactly `dα+dβ` and `dα-dβ`. Thus smooth assembly is no longer an open
interface. The remaining differential theorem is to decide which obstruction
vanishes from the curvature hypotheses, or to state their nonvanishing as the
sharp obstruction.

More precisely, the formal classifier proves four mutually exhaustive cases:

`plus only ⇔ dα=-dβ and dα≠0`,

`minus only ⇔ dα=dβ and dα≠0`,

`both ⇔ dα=dβ=0`,

`neither ⇔ dα≠dβ and dα≠-dβ`.                         (6.9)

For a local patch, nonzero witnesses for `dα+dβ` and `dα-dβ` may occur at
different points and still reject both global candidates. Equation (6.9) is
an exact decision interface, not a claim that the intended metric hypotheses
force a particular class.

## 7. Polynomial obstruction and false positives

The proposed characteristic factorization

`det(λI-𝓡)=(λ²-q²)(λ²-Rλ-c)`                              (7.1)

implies the coefficient obstruction

`C_KK=e₁²e₄-e₁e₂e₃+e₃²=0`.                              (7.2)

Lean verifies this implication and the generic recovery formula
`q²=-e₃/e₁`. It also verifies an explicit real coefficient tuple satisfying
(7.2) with reconstructed `q²<0`, hence with no real protected pair. Equation
(7.2) is therefore only a necessary filter, not a reconstruction theorem.

## 8. Relation to prior work

Krongos and Torre give separate metric geometrization and reconstruction
conditions for scalar and Maxwell fields. Bergqvist and Höglund develop
algebraic Rainich theory in higher dimensions, including a complete
five-dimensional algebraic generalization. Costa, Naves de Oliveira, and
Guimarães use generalized Rainich algebra in symmetry-reduced scalar--tensor
EMD cosmic-string solutions. Lü, Mao, and Wu provide the convention-fixed EMD
equations and five-dimensional Kaluza origin used here.

The proposed contribution is not the observation that a dilaton modifies
Rainich algebra. It is the generic coupled block classification, its exact
Lorentzian admissibility conditions, and the discrete centralizer obstruction
to pointwise uniqueness. This novelty assessment remains provisional until an
independent specialist completes the literature and statement audit.

## 9. Limitations and next theorem

The present result assumes a real diagonalizable generic spectral branch and
excludes additional eigenvalue-sum resonances. It does not yet:

1. derive the full characteristic factorization as a tensor theorem;
2. assemble every spectral block on the full Lorentzian tangent space;
3. classify zero-trace, null-Maxwell, null-scalar, or repeated-eigenvalue
   branches;
4. prove existence, uniqueness, or nonexistence for the two explicit smooth
   scalar-branch obstruction matrices;
5. reconstruct a Maxwell two-form or impose Maxwell and scalar equations;
6. prove a local necessary-and-sufficient Kaluza uplift theorem.

These are explicit targets, not implicit claims of the present paper.

## 10. Formal verification and reproducibility

The Lean and Mathlib versions are pinned. Run

```text
lake update
lake exe cache get
bash scripts/audit.sh
```

The audit rejects `sorry`, `admit`, and project-declared axioms, builds the
library, and prints the axiom dependencies of every advertised theorem. A
theorem-to-Lean translation table appears in `LEAN_MAP.md`.

## AI contribution disclosure

Under human direction, OpenAI Codex proposed and developed the generic
reconstruction calculation, produced the Lean formalization, identified the
relative-sign nonuniqueness during adversarial review, formulated the
centralizer interpretation, surveyed the relevant literature, and drafted the
research artifact. The human collaborators chose the research direction,
reviewed the scope and publication decisions, and retain responsibility for
the claims. Because the same AI system contributed to the informal statements
and their formalization, the artifact should be described as Lean-checked with
statement correspondence unaudited until an independent review is obtained.

## References

- G. Bergqvist and A. Höglund, *Algebraic Rainich Theory and
  Antisymmetrisation in Higher Dimensions* (2002),
  <https://arxiv.org/abs/gr-qc/0202092>.
- M. L. Costa, A. L. Naves de Oliveira, and M. E. X. Guimarães, *On the
  Generalized Rainich Algebra in Scalar-Tensor Gravities* (2006),
  PoS(IC2006)061.
- D. S. Krongos and C. G. Torre, *Geometrization Conditions for Perfect
  Fluids, Scalar Fields, and Electromagnetic Fields* (2015),
  <https://arxiv.org/abs/1503.06311>.
- H. Lü, P. Mao, and J.-B. Wu, *Asymptotic Structure of
  Einstein-Maxwell-Dilaton Theory and Its Five Dimensional Origin* (2019),
  <https://arxiv.org/abs/1909.00970>.
