# High-impact Rainich--Kaluza program

Date adopted: 2026-08-10

## North-star result

The project now aims at a constructive local recognition theorem of the
following form.

> On an explicitly stated generic Lorentzian branch, a four-dimensional
> metric is locally the circle reduction of a five-dimensional Ricci-flat
> metric if and only if it satisfies a finite list of intrinsic curvature and
> curvature-derivative conditions. When the conditions hold, the scalar,
> Maxwell duality orbit, EMD coupling magnitude, and five-dimensional metric
> can be constructed locally from the four-dimensional metric. The theorem
> classifies all discrete and degenerate ambiguities.

This statement is a target, not a current theorem. Its value would be the
coupled and constructive nature of the result: separate scalar and Maxwell
geometrization theorems are known, but the Ricci tensor here contains only
their sum.

## What would count as a field-level contribution

The work should produce at least one of the following, preferably the first
two together:

1. a finite-order necessary-and-sufficient metric-only Kaluza uplift theorem;
2. an intrinsic differential reconstruction of the EMD coupling magnitude
   `a²`, with Kaluza gravity recognized by `a²=3`;
3. a uniqueness theorem or a genuine two-uplift theorem for the discrete
   scalar reflection branches;
4. a new exact Kaluza solution generated from the curvature-only conditions;
5. extraction of hidden scalar multipoles from four-dimensional curvature,
   confirmed on exact rotating solutions and tied to a clean observable.

Lean verification is a correctness multiplier for these results. It is not a
substitute for their mathematical-physics novelty.

## Generic branch for the first theorem

The initial local theorem may assume:

- a smooth four-dimensional Lorentzian manifold;
- non-null Maxwell sector, so the Maxwell stress has real `+q` and `-q`
  principal planes with `q>0`;
- nonzero, non-null scalar gradient;
- real diagonalizable mixed Ricci endomorphism with the required spectral
  gaps and no extra eigenvalue-sum resonances;
- constant ranks and smooth spectral projectors on a simply connected
  neighborhood.

Every excluded branch must be listed. None may be silently absorbed into the
word “generic.”

## Phase I — recover the differential coupling

Use the convention-fixed action

`L = √(-g)[R - ¼ exp(aφ) F² - ½(dφ)²]`.

Define

`v=dφ`, `𝓕=exp(aφ/2)F`.

The Bianchi and Maxwell equations become

`d𝓕 = (a/2) v∧𝓕`,

`d(*𝓕) = -(a/2) v∧(*𝓕)`.                              (HC1)

Unlike the pointwise Einstein equation, (HC1) contains `a` explicitly. The
first goal is to express all four terms in (HC1) through reconstructed
curvature data and prove:

- existence of a common constant coupling is an intrinsic differential
  condition;
- on a nondegenerate wedge channel that coupling is unique after fixing the
  global orientation of `v`;
- changing `v→-v` changes `a→-a`, so the convention-independent metric datum
  is `a²`;
- the Kaluza branch is selected by `a²=3`.

### Phase-I exit criterion

An explicit curvature-derived compatibility tensor or scalar `a_geom²`, a
proof of its branch behavior, and positive/adversarial exact-metric tests.

Current status: the rescaled identities are convention-checked, and Lean
proves abstract uniqueness of the signed coupling on either nonzero channel,
an explicit linear-probe recovery formula, and invariance of `a²` under the
global scalar-orientation reversal. On the non-null three-form branch, Lean
also verifies the coordinate-free Lorentzian-pairing formulas

`a = 2⟪d𝓕,v∧𝓕⟫ / ⟪v∧𝓕,v∧𝓕⟫`,

`a² = 4⟪d𝓕,d𝓕⟫ / ⟪v∧𝓕,v∧𝓕⟫`,

including agreement of the primal and dual channels. Reconstruction of these
channel data from curvature is the next step.

## Phase II — settle differential branch selection

Construct the two smooth scalar covector candidates from spectral projectors,
not from a chosen eigenbasis. For candidates `v₊=α+β` and `v₋=α-β`, the
repository already proves abstractly that both can be closed only if
`dα=dβ=0`.

The remaining work is to:

- instantiate `d` as exterior differentiation on the smooth one-form bundle;
- express `dα` and `dβ` through curvature and derivatives of the projectors;
- prove whether generically zero, one, or two branches satisfy closure and
  (HC1);
- classify the exceptional separately integrable locus.

Current status: on any invariant block obeying
`(R-aI)(R-bI)=0`, the eigenvector-free polynomial
`Pₐ=(R-bI)/(a-b)` is Lean-verified to be an idempotent commuting with `R`, to
act as identity on the `a` eigenspace and as zero on the `b` eigenspace, and to
generate the corresponding involutive reflection. Extending these projectors
to the full four-root Ricci splitting and differentiating them are the next
geometric steps.

### Phase-II exit criterion

A coordinate-free uniqueness theorem, a genuine two-uplift theorem, or a
sharp curvature obstruction explaining why neither branch closes.

## Phase III — reconstruct the Maxwell two-form

For each admissible scalar branch set `S=𝓡-V`. Impose the algebraic Maxwell
Rainich conditions and construct a local two-form `𝓕` up to complexion. Then
use (HC1) to determine the complexion differential and coupling
simultaneously.

This phase must distinguish:

- Maxwell stress reconstruction;
- two-form reconstruction up to duality;
- Bianchi and Maxwell differential closure;
- residual constant duality and orientation freedoms.

### Phase-III exit criterion

A complete local list of reconstructed `(v,𝓕,a)` orbits determined by the
metric on the generic branch.

## Phase IV — constructive five-dimensional uplift

Integrate the closed scalar covector locally, construct `F` from `𝓕`, obtain a
local potential `A`, and assemble the convention-fixed Kaluza metric

`ĝ = exp(c₁φ) g + exp(c₂φ)(dz + c₃A)²`,

with all constants derived from the chosen normalization. Prove directly that
the reconstructed five-dimensional metric is Ricci-flat and prove the
converse reduction statement.

### Phase-IV exit criterion

The north-star local if-and-only-if theorem, including uniqueness and all
stated gauge/discrete freedoms.

## Phase V — exact, adversarial, and generative tests

Minimum validation set:

1. a rotating dyonic `a=√3` solution passes and reconstructs a Ricci-flat
   uplift;
2. an analogous `a≠√3` EMD solution passes pointwise algebra but returns its
   non-Kaluza value of `a_geom²`;
3. scalar-plus-fluid or other mixed matter is rejected;
4. null, trace-zero, and eigenvalue-collision examples are routed to explicit
   degenerate branches rather than producing false positives.

The generative moonshot is to impose the curvature-only conditions on a new
metric ansatz and obtain a previously unknown exact Kaluza solution.

## Phase VI — observable mathematical physics

Only after the local theorem is secure:

- rebuild the rotating equal-dyon scalar-dipole calculation from cited exact
  solutions;
- determine whether the dipole and translated quadrupole can be extracted
  directly from asymptotic four-dimensional curvature;
- derive waveform modes and approximation order with independent analytic or
  numerical-relativity checks;
- reconnect the laboratory scalar-amplifier branch only if its EFT coupling
  has a defensible geometric origin and phenomenologically allowed scale.

## Kill criteria

The program should change direction if:

- the coupled differential conditions reduce trivially to separately known
  scalar and Maxwell reconstruction with no new orbit or compatibility
  content;
- the coupling cannot be identified even up to sign from any finite-order
  local curvature data, in which case the correct result should be a no-go
  theorem;
- generic smooth spectral projectors fail in the physically relevant
  Lorentzian branch;
- exact Kaluza and non-Kaluza EMD metrics cannot be separated by the proposed
  differential classifier.

A rigorous no-go or nonuniqueness theorem meeting one of these criteria may be
as valuable as the intended reconstruction theorem.
