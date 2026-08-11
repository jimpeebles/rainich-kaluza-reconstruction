# Research-program synthesis

Date: 2026-08-10

This note re-synthesizes the connected research conversations rather than
treating their latest artifacts as independent projects. It is an internal
decision document, not a novelty claim.

## The common question

The historical Rainich and Kaluza programs approached the same ambition from
opposite directions:

- Rainich asked which matter fields are already encoded in four-dimensional
  curvature.
- Kaluza showed that five-dimensional vacuum curvature reduces to a
  four-dimensional metric, Maxwell field, and scalar radius.

The present project asks whether these statements can be joined into a local,
metric-first recognition theorem:

`4-D curvature → scalar + Maxwell reconstruction → √3-EMD checks → candidate 5-D vacuum uplift`.

This is the mathematical spine of the wider effort.

## What the conversation cluster established

### 1. Generalized Rainich--Kaluza reconstruction

This is the primary line. The pointwise Ricci tensor is a sum of a Maxwell
endomorphism and a rank-one scalar endomorphism. The repository has proved the
rank-one square law, the resulting noncommutative reconstruction equation,
generic complementary-block admissibility, and a discrete relative-sign
ambiguity. The ambiguity is intrinsic: a Ricci-centralizing spectral
reflection exchanges the two scalar tensors while preserving the curvature
data.

The protected-eigenspace theorem and its new four-dimensional composition
close the algebraic entrance. A
rank-one perturbation cannot remove an eigenvalue carried by a two-dimensional
eigenspace. Dimension four, trace zero, and `S²=q²I` now Lean-prove that both
Maxwell polynomial projector ranges have rank two. Hence they protect one
`+q` and one `-q` Ricci eigendirection, and these are machine-checked roots of
the actual characteristic polynomial. Canonical coefficient extraction and
the polynomial converse then force the full `(x²-q²)` factor and the
necessary obstruction. Only the Maxwell square law remains an established
algebraic input at this entrance.

### 2. Exact Kaluza solutions and scalar multipoles

The earlier calculations indicate that rotating equal dyons can have vanishing
scalar monopole but a spin-directed scalar dipole, with a translated-dipole
quadrupole in multi-centre solutions. This is potentially observable
mathematical physics and is the best downstream testbed for reconstruction.
It is not yet part of this repository's proved surface: the source solutions,
normalizations, asymptotic expansions, and radiation approximation must be
rebuilt reproducibly here before any claim is reused.

### 3. Critical scalar/EM cavity amplifier

The cavity work identified a coherent quadratic scalar--photon mode-conversion
mechanism, selection rules, a Manley--Rowe-like energy partition, and a
speculative material-trapping window. Those are interesting conditional EFT
results, but they do not establish a Kaluza origin or an accessible coupling in
nature. The amplifier remains quarantined as a later application until the
geometric EFT provenance, phenomenological constraints, and finite-volume
spectral problem are independently secured.

## Epistemic map

| Layer | Current status | Research use |
|---|---|---|
| Classical Maxwell and scalar Rainich theory | established literature | ingredients and comparison baseline |
| `a=√3` EMD from five-dimensional vacuum gravity | established, convention-sensitive | selects the physical theory |
| Coupled pointwise block reconstruction and its two-branch ambiguity | Lean-checked in this repository | present core result |
| Protected `±q` directions under the scalar rank-one perturbation | Lean-checked from the four-dimensional tracefree square-law hypotheses | completed algebraic entrance |
| Full characteristic factorization from four-dimensional Maxwell algebra | Lean-checked for `S+V` with square-law `S` and rank-one `V` | necessary pointwise theorem; not sufficient for reconstruction |
| Differential selection/identification of pointwise partners | open | decisive local-reconstruction target |
| Maxwell two-form recovery and scalar/Maxwell field equations | open | required for sufficiency and for identifying `a=√3` |
| Exact-solution scalar multipoles and binary hierarchy | promising inherited derivation, unreproduced here | strongest physics validation track |
| Laboratory critical amplifier | conditional and speculative | downstream falsifiable application only |

## Why differential closure is the high-impact frontier

Pointwise Ricci algebra cannot identify the Kaluza coupling: at a point the
factor `exp(√3 φ)` can be absorbed into a rescaled Maxwell two-form. It also
cannot choose between the reflection-related scalar tensors found in this
repository. Derivatives are therefore not technical decoration; they contain
the information that pointwise curvature necessarily loses.

The two pointwise partners have now been promoted, on explicit
simple-spectrum/strict-sign patches, to smooth spectral one-form jets with
machine-checked obstruction matrices `dα±dβ`. The next theorem should
determine what those two obstruction matrices do. There are three
possibilities, each scientifically useful:

1. only one branch generically admits a closed covector factor, yielding local
   selection;
2. both do, revealing a genuine local discrete duality of the coupled system;
3. neither does without an additional curvature condition, identifying the
   missing differential invariant.

Any of these outcomes improves our understanding of the inverse problem.

## Research sequence now adopted

1. Promote the pointwise spectral projectors and amplitude formulas to smooth
   curvature-derived tensor fields and compute the branch obstruction forms.
   **Complete on the explicit generic coordinate patch.**
2. Formulate differential closure at the tensor level without prematurely
   choosing a scalar sign; classify the reflection-related branches.
3. Reconstruct the residual Maxwell stress and impose classical Rainich
   differential closure.
4. Use the scalar and Maxwell equations to identify the EMD coupling, then
   specialize to `a=√3` and state the local Kaluza-uplift criterion.
5. Rebuild at least two exact positive tests and two adversarial non-Kaluza
   tests with reproducible conventions.
6. Only then reconnect the scalar-multipole and laboratory tracks.

The publication target is therefore a coupled local geometrization theorem or
a sharp no-go/classification theorem discovered on the way. A collection of
isolated polynomial identities is not the target.
