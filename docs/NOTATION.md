# Notation and convention registry

> Supporting cross-reference only.  The convention authority for the active
> paper is [`EMD_CONVENTION.md`](EMD_CONVENTION.md); resolve any discrepancy in
> its favor.

No calculation should enter the theorem surface until its convention is fixed
here.

| Symbol | Intended meaning | Status |
|---|---|---|
| `g` | four-dimensional Lorentzian metric | signature `(-,+,+,+)` |
| `R^μ_ν` | mixed Ricci endomorphism | active candidate object |
| `R` | Ricci scalar / trace of the mixed Ricci endomorphism | active |
| `φ` | canonically normalized Kaluza scalar in `-½(∂φ)²` convention | fixed |
| `v` | `dφ` | local candidate |
| `V` | `½ v^♯ ⊗ v` | fixed by the EMD Einstein equation |
| `F` | Maxwell two-form `dA` | fixed |
| `𝓕` | exponentially rescaled physical form `e^(aφ/2)F` | fixed |
| `H` | Ricci-residual-normalized form `𝓕/√2`; its ordinary Maxwell stress is `S` | fixed |
| `S` | `½e^(aφ)` times the traceless Maxwell stress endomorphism | fixed |
| `q²` | `e^(2aφ)[(F²)²+(F·*F)²]/64` in `S²=q²I` | fixed on the non-null branch |
| `e₁,…,e₄` | elementary characteristic coefficients | fixed by `det(λI-R)=λ⁴-e₁λ³+e₂λ²-e₃λ+e₄` |
| `C_KK` | `e₁²e₄-e₁e₂e₃+e₃²` | candidate necessary obstruction |

The two uses of `R`—endomorphism and scalar trace—must be typographically
distinguished in the paper, for example `\mathsf R` versus `R`.

The full derivation and scope boundary are recorded in
`docs/EMD_CONVENTION.md`.
