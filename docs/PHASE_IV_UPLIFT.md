# Phase IV — constructive five-dimensional uplift

## Verified entry data

Phase IV now begins with an accepted generic local branch carrying:

- an open convex coordinate patch `U`;
- the unique generic closed relative-sign scalar branch `v`;
- a local scalar potential `φ`, with `v=dφ`, unique up to an additive
  constant and the global orientation reversal;
- a reconstructed rescaled Maxwell orbit `(𝓕,*𝓕)` and coupling `a` whose two
  Phase-III obstruction forms vanish;
- the physical Maxwell field `F=exp(-aφ/2)𝓕`, proved closed at the first-jet
  exterior level;
- the closed weighted dual flux `exp(aφ/2)*𝓕`;
- the Kaluza test `a²=3`, with one scalar orientation giving `a=√3`.

The Lean entry theorems are
`relativeSign_scalarPotential_exists_unique_branch`,
`exists_scalarPotential_of_closed`,
`hasFDerivAt_negativeEMDWeight`,
`hasFDerivAt_positiveEMDWeight`,
`localPositiveQ_obstructions_give_closed_exponentialWeightJets`, and
`kaluzaCoupling_has_positive_orientation`.

This is conditional on the upstream curvature construction producing at least
one closed scalar branch. Null, repeated-root, and global topological cases
remain outside the generic local claim.

## IV.1 — integrate the closed two-form

Phase IV now contains the first verified part of a constructive Poincare
argument for the physical two-form. The pinned Mathlib version contains the
needed one-form theorem but does not expose a directly reusable real two-form
version in the current search surface. On a star-shaped coordinate patch the
development defines the standard radial homotopy operator

`A_i(x) = ∫₀¹ t x^j F_{ji}(t x) dt`.

Lean now proves:

- continuity of `F` makes the radial integrand interval-integrable;
- `A(0)=0` and alternating `F` gives the radial gauge condition `A_x(x)=0`;
- Mathlib's dominated local-Lipschitz theorem supplies an honest
  componentwise differentiation-under-the-integral bridge, with every
  measurability, integrability, and domination hypothesis exposed;
- the closedness cyclic identity converts antisymmetrization of the formal
  derivative integrand into the derivative of `t²F(tx)`;
- the fundamental theorem of calculus then proves that the integrated
  derivative candidate has curvature exactly `F`;
- at a point, every alternating `F` has a potential first jet, and two such
  jets differ by a symmetric jet.

The main Lean theorems are `radialGaugePotential_self_eq_zero`,
`hasFDerivAt_radialGaugePotentialEvaluation_of_dominated_loc_of_lip`,
`integral_radialCurvatureIntegrand_eq`, and
`radialPotentialDerivativeCandidate_curvature`.

The remaining analytic splice is to derive the displayed derivative candidate
itself from a convenient regularity package for `F`, discharging the dominated
differentiation hypotheses uniformly for every evaluation direction. Once
that is connected, the result is the desired theorem

`dF=0  →  dA=F`.

Then prove the local gauge orbit: if `dA=dA'=F`, there is a scalar `χ` with

`A'=A+dχ`.

The second statement is now complete: Lean proves that equal curvature makes
`A'-A` a closed one-form, then reuses the verified one-form Poincare lemma to
obtain `A'=A+dχ`; `χ` is unique up to an additive constant. The theorem is
`exists_localGaugeParameter_of_same_curvature`, with uniqueness supplied by
`localGaugeParameter_unique_up_to_constant`.

## IV.2 — fix the uplift convention before assembly

Derive—not import by memory—the constants in

`ĝ = exp(c₁φ) g + exp(c₂φ) (dz + c₃A)²`

from the five-dimensional Einstein-Hilbert action and the convention-fixed
four-dimensional action in `docs/EMD_CONVENTION.md`. In particular, record:

- the sign relating the Kaluza radius scalar to the repository's `φ`;
- the normalization of `A` relative to the `-¼ exp(√3φ)F²` term;
- the circle-coordinate normalization and signature;
- the transformation of `z` accompanying `A↦A+dχ`;
- the effect of the additive constant in `φ` on circle radius and coordinate
  rescaling.

Only after this derivation should `c₁,c₂,c₃` become Lean definitions.

The convention-independent gauge algebra is already verified. Lean constructs
the full bilinear block metric, proves it symmetric whenever `g` is symmetric,
and proves it nondegenerate whenever `g` is nondegenerate and both warp factors
are nonzero. The fiber one-form `dz+cA` and the full warped metric pairing
`u g + v(dz+cA)²` are invariant under

`A ↦ A+dχ`, `ξ ↦ ξ-c dχ(X)`,

and the shifts compose additively. This completes the convention-independent
assembly algebra without prematurely choosing `u`, `v`, or `c`; signature and
inverse formulas still require the convention-fixed coefficients.

## IV.3 — assemble and verify the metric

Construct the five-dimensional block metric and prove:

1. symmetry, nondegeneracy, and Lorentz signature;
2. invariance under the local Kaluza gauge transformation;
3. explicit inverse-metric formulas;
4. Christoffel and Ricci block identities;
5. the forward theorem: the convention-fixed four-dimensional EMD equations
   imply `Ric(ĝ)=0`;
6. the converse theorem: a circle-invariant Ricci-flat metric in the stated
   ansatz reduces to those EMD equations.

The block Ricci calculation should first be proved in a coordinate algebra
layer with named reusable identities. A later manifold wrapper can then state
the coordinate-free local uplift theorem without hiding the computational
core.

## IV.4 — uniqueness and exit condition

Classify the complete local uplift freedom:

- scalar orientation and the corresponding sign of `a`;
- additive constant of `φ` and circle-radius normalization;
- Maxwell gauge `A↦A+dχ` paired with the circle-coordinate shift;
- overall Maxwell sign where it survives;
- choice of local circle coordinate.

Phase IV exits only when the forward and converse Ricci-flatness theorems and
this orbit classification are all proved. Exact-solution tests belong to
Phase V and do not substitute for these identities.
