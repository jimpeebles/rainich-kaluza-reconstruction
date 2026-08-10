# Generic eigenbasis reconstruction

This note records the strongest exact result currently in the repository and
the assumptions separating it from the intended geometric theorem.

## Setup

The convention-fixed origin of the decomposition below is given in
`docs/EMD_CONVENTION.md`. Assume the mixed Ricci endomorphism is
real-diagonalizable at a point with
spectrum

`{q, -q, a, b}`

and trace `T = a + b`. Assume also that the Maxwell part obeys `S² = q² I` and
the scalar contribution is rank one with trace `T`, hence obeys `V² = T V`. The
noncommutative theorem `reconstructionEquation_of_decomposition` then derives

`R V + V R - T V = R² - q² I`.                         (GR1)

This derivation is coordinate-free and valid in any associative real algebra.
The decomposition and scalar square law now have convention-fixed provenance
from the `a=√3` EMD Einstein equation. The Maxwell square law remains an
established four-dimensional Rainich identity rather than a formalized
exterior-algebra theorem in this repository.

In an eigenbasis, each matrix component satisfies

`(λᵢ + λⱼ - T) Vⁱⱼ = δⁱⱼ(λᵢ²-q²)`.                    (GR2)

Equation (GR2) immediately distinguishes three types of component.

## Protected eigendirections

For `λ = ±q`, the diagonal right-hand side vanishes. Provided
`2λ-T ≠ 0`, the corresponding diagonal entry of `V` vanishes. All
off-diagonal entries involving a protected eigendirection also vanish unless
an additional eigenvalue-sum resonance occurs.

## Complementary two-dimensional block

Because `a+b=T`, equation (GR2) leaves the `a,b` off-diagonal entries
unconstrained. It fixes the diagonal entries to

`u = (a²-q²)/(a-b)`,

`v = (b²-q²)/(b-a)`.

The Lean development proves two useful identities:

`u+v = a+b = T`,

`uv = -((a²-q²)(b²-q²))/(a-b)²`.

Thus trace compatibility is automatic rather than an extra field equation.

## Rank-one and real-completion criterion

A real symmetric rank-one completion of the block exists precisely when

`uv ≥ 0`,

or equivalently

`(a²-q²)(b²-q²) ≤ 0`.                                  (GR3)

Condition (GR3) says that `q²` lies between `a²` and `b²` in product order.
It is a new candidate admissibility inequality emerging from the
reconstruction calculation. It is not by itself the Lorentzian condition.

## Lorentzian scalar factorization

Let the pseudo-orthonormal metric signs of the two complementary
eigendirections be `εₐ, ε_b ∈ {±1}`. A real scalar covector with components
`x,y` produces the mixed tensor block

`Vᵃₐ = εₐ x²/2`,  `Vᵇ_b = ε_b y²/2`,

`Vᵃ_b = εₐ xy/2`, `Vᵇₐ = ε_b xy/2`.

The repository proves that prescribed mixed diagonal entries `u,v` admit such
a factorization if and only if

`εₐu ≥ 0` and `ε_bv ≥ 0`.                              (GR4)

It also proves both the rank-one determinant identity and metric
self-adjointness after lowering the raised index. Equation (GR4), not merely
`uv≥0`, is the correct pointwise scalar-factorization condition in a fixed
Lorentzian signature assignment.

The packaged theorem `exists_scalarComplementaryBlock_iff` goes one step
further: it quantifies over scalar components and proves that a
scalar-generated block solving all four complementary component equations
exists exactly under the two inequalities in (GR4). The companion theorem
`solvesComplementaryBlock_iff` classifies every solution of those component
equations and makes the off-diagonal resonance explicit.

On the nondegenerate branch where the first component is nonzero,
`scalarMixedBlock_components_unique_up_to_sign` additionally proves that two
component pairs generating the same mixed block agree up to the simultaneous
global sign. This is factorization uniqueness for a **fixed tensor**, not
uniqueness of the tensor reconstructed from curvature.

## Relative-sign ambiguity and centralizer orbit

When both scalar components are nonzero, reversing only one of them changes
both off-diagonal mixed entries while preserving the two forced diagonals. The
new block still solves every complementary Sylvester equation and is distinct
from the original block.

The repository proves more than existence of this counterpartner:

- any two scalar-generated generic solutions are equal or relative-sign
  partners;
- the partner is obtained by conjugation with the involution
  `diag(1,-1)` on the complementary eigenspace;
- that involution commutes with `diag(a,b)` and hence leaves the Ricci block
  unchanged;
- in any associative real algebra, every involution commuting with `𝓡` maps a
  reconstruction-equation solution to another solution by conjugation.
- an idempotent spectral projector `P` constructs such an involution
  basis-independently as `J=I-2P`.

Therefore pointwise curvature algebra determines an orbit under the Ricci
centralizer, not a unique rank-one tensor. This is an intrinsic obstruction;
calling it “eigenvector orientation freedom” would understate the fact that the
two tensors themselves are distinct.

## What remains before this is a geometric theorem

1. Formalize the four-dimensional Maxwell square law from exterior algebra,
   or state it explicitly as a named literature input.
2. Prove the spectral factorization and existence of the required real
   pseudo-orthonormal eigenbasis on the stated generic branch.
3. Classify all eigenvalue-sum resonances excluded above.
4. Assemble the complementary classification on the full tangent space using
   the now-formalized idempotent-reflection construction.
5. Convert the pointwise scalar covector into a smooth local one-form and
   impose closure.
6. Reconstruct the Maxwell field and impose the differential Rainich and
   scalar equations.

Until these steps are complete, the result should be described as a
machine-checked generic pointwise block classification and uniqueness
obstruction, not a generalized Rainich–Kaluza theorem.
