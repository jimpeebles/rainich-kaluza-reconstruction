# Convention-fixed EMD provenance

This note fixes the normalization used by the algebraic reconstruction layer.
It follows equations (1)--(4) of Lü, Mao, and Wu, *Asymptotic Structure of
Einstein-Maxwell-Dilaton Theory and Its Five Dimensional Origin* (2019),
<https://arxiv.org/abs/1909.00970>.

## Action and Kaluza coupling

Use Lorentz signature `(-,+,+,+)` and

`L = √(-g) [ R - ¼ e^(aφ) F_{μν}F^{μν} - ½ ∂_μφ ∂^μφ ]`,

with `F=dA`. The Kaluza reduction of five-dimensional vacuum gravity is the
case `a=√3` in this normalization.

The rearranged Einstein equation is

`R_{μν} = ½ e^(aφ) (F_{μρ}F_ν{}^ρ - ¼ g_{μν}F²)
          + ½ ∂_μφ ∂_νφ`.                              (E1)

Its trace is

`R = ½ (∂φ)²`.                                         (E2)

## Mixed-endomorphism decomposition

Let `v_μ=∂_μφ` and raise the first index in (E1). Define

`S^μ{}_ν = ½ e^(aφ)(F^{μρ}F_{νρ} - ¼ δ^μ{}_ν F²)`,

`V^μ{}_ν = ½ v^μv_ν`.

Then the mixed Ricci endomorphism satisfies

`𝓡 = S + V`,                                           (E3)

and `tr(S)=0`, `tr(V)=R`.

The scalar part is rank one. In basis-free language it is the endomorphism
`y ↦ ½ v(y) v^♯`. Therefore

`V² = tr(V) V = R V`.                                  (E4)

Theorem `rankOneEndomorphism_sq_eq_trace_smul` proves (E4) for every finite
free real module, independently of coordinates.

## Maxwell square law

For the four-dimensional Maxwell stress endomorphism

`T^μ{}_ν = F^{μρ}F_{νρ} - ¼ δ^μ{}_ν F²`,

the classical algebraic Rainich identity is

`T² = 1/16 [(F_{μν}F^{μν})² + (F_{μν}(*F)^{μν})²] I`.

Consequently the scaled Maxwell part in (E3) satisfies

`S² = q² I`,

`q² = e^(2aφ)/64 [(F²)² + (F·*F)²]`.                  (E5)

On the non-null Maxwell branch `q²>0`. The project treats (E5) as an
established four-dimensional Rainich input; a future tensor-library layer may
formalize its exterior-algebra derivation.

## Reconstruction equation

Equations (E3)--(E5) imply, without assuming that `S` and `V` commute,

`𝓡V + V𝓡 - R V = 𝓡² - q²I`.                           (E6)

This noncommutative implication is Lean-verified by
`reconstructionEquation_of_decomposition`.

## Scope boundary

This note fixes the pointwise Einstein-equation provenance. It does not assume
or prove the Maxwell equation, scalar equation, closure of a reconstructed
one-form, or five-dimensional local uplift. Those are differential closure
obligations for the larger project.

