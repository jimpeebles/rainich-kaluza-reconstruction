import RainichKaluza.KaluzaBlockAssembly

/-!
# Kaluza Christoffel blocks in normal-gauge evaluated jets

First half of the Phase-IV.3 block-curvature calculation: the six Christoffel
blocks of the warped Kaluza metric, computed in the coordinate algebra layer
at a *normal-gauge point*.

The evaluation point is prepared by two Lean-verified freedoms: normal
coordinates for the base metric (`g = diag d`, `∂g = 0` at the point — the
manifold wrapper's obligation), and the Kaluza gauge shift
(`kaluzaMetricPairing_gauge_invariant`) putting the potential in radial
gauge, `A = 0` at the point, while `∂A` survives.  The warp factors carry
log-derivatives `k₁, k₂` — the evaluated form of the verified exponential
derivatives (`hasFDerivAt` of `exp(kφ)` gives `∂(e^{kφ}) = k·φ₁·e^{kφ}`).

`kaluzaNormalGaugeMetricJet` assembles the resulting first derivative of the
block metric; `kaluzaNormalGaugeChristoffel` is the raw Christoffel formula
`Γ^M_{NP} = ½ ĝ^{MQ}(∂_N ĝ_{QP} + ∂_P ĝ_{QN} - ∂_Q ĝ_{NP})` applied to it.
The six block theorems below evaluate it in closed form:

* base-base-base: the pure conformal-warp connection
  `(k₁/2)(δ^μ_ν φ₁_ρ + δ^μ_ρ φ₁_ν - g_{νρ} φ₁^μ)`;
* base-base-fiber: the Maxwell shear `(vc/2u) F_ν{}^μ` — under the derived
  convention the prefactor is exactly the EMD weight `e^{√3 φ}`
  (`conventionKaluzaWarpRatio`);
* base-fiber-fiber: the fiber-gradient force `-(k₂v/2u) φ₁^μ`;
* fiber-base-base: the symmetrized gauge jet `(c/2)(∂_ν A_ρ + ∂_ρ A_ν)`;
* fiber-base-fiber: the dilaton rate `(k₂/2) φ₁_ν`;
* fiber-fiber-fiber: zero.

The Ricci blocks and the forward/converse Ricci-flatness theorems assemble
on top of these identities together with the second-derivative jets; that is
the remaining half of IV.3.
-/

namespace RainichKaluza

open Matrix

section NormalGaugeJet

/-- Evaluated first derivative of the Kaluza block metric at a normal-gauge
point: base metric `diag d` with vanishing first jet, potential vanishing at
the point, warp values `u, v` with log-derivatives `k₁, k₂`, scalar jet
`phi1`, and gauge jet `A1 ρ μ = ∂_ρ A_μ`.  Circle derivatives vanish. -/
def kaluzaNormalGaugeMetricJet (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ)
    (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ) :
    (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → ℝ
  | Sum.inl rho, Sum.inl mu, Sum.inl nu =>
      k₁ * phi1 rho * u * Matrix.diagonal d mu nu
  | Sum.inl rho, Sum.inl mu, Sum.inr _ => v * c * A1 rho mu
  | Sum.inl rho, Sum.inr _, Sum.inl nu => v * c * A1 rho nu
  | Sum.inl rho, Sum.inr _, Sum.inr _ => k₂ * phi1 rho * v
  | Sum.inr _, _, _ => 0

/-- The assembled metric jet is symmetric in its two metric slots. -/
theorem kaluzaNormalGaugeMetricJet_symm (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ)
    (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (R M N : Fin 4 ⊕ Unit) :
    kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1 R M N =
      kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1 R N M := by
  rcases R with rho | _ <;> rcases M with mu | _ <;> rcases N with nu | _ <;>
    simp [kaluzaNormalGaugeMetricJet, Matrix.diagonal_apply, eq_comm]
  rcases eq_or_ne mu nu with rfl | h
  · rfl
  · simp [h]

/-- Evaluated inverse block metric at the normal-gauge point: with `A = 0`
the inverse is block diagonal, `u⁻¹ diag(d)⁻¹ ⊕ v⁻¹`. -/
noncomputable def kaluzaNormalGaugePointInverse (u v : ℝ) (d : Fin 4 → ℝ) :
    (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → ℝ
  | Sum.inl mu, Sum.inl sigma => if mu = sigma then u⁻¹ * (d mu)⁻¹ else 0
  | Sum.inr _, Sum.inr _ => v⁻¹
  | _, _ => 0

/-- Consistency with the assembly layer: the normal-gauge point inverse is
the entrywise value of `kaluzaBlockMetricInverse` at vanishing potential and
diagonal base inverse. -/
theorem kaluzaNormalGaugePointInverse_eq_blockInverse
    (u v c : ℝ) (d : Fin 4 → ℝ) (M N : Fin 4 ⊕ Unit) :
    kaluzaNormalGaugePointInverse u v d M N =
      kaluzaBlockMetricInverse u v c
        (Matrix.diagonal fun i => (d i)⁻¹) (fun _ => 0) M N := by
  rw [kaluzaBlockMetricInverse_eq_fromBlocks]
  rcases M with mu | u1 <;> rcases N with nu | u2
  · simp only [kaluzaNormalGaugePointInverse, Matrix.fromBlocks_apply₁₁,
      Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite,
      mul_zero]
  · simp [kaluzaNormalGaugePointInverse, oneFormColumn, Matrix.mul_apply]
  · simp [kaluzaNormalGaugePointInverse, oneFormRow, Matrix.mul_apply]
  · simp [kaluzaNormalGaugePointInverse, oneFormColumn, oneFormRow,
      Matrix.mul_apply]

/-- Christoffel symbols of the first kind assembled from the metric jet:
`Γ_{Q,NP} = ½(∂_N ĝ_{QP} + ∂_P ĝ_{QN} - ∂_Q ĝ_{NP})`. -/
noncomputable def kaluzaNormalGaugeChristoffelFirstKind (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (Q N P : Fin 4 ⊕ Unit) : ℝ :=
  (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1 N Q P +
    kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1 P Q N -
    kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1 Q N P) / 2

/-- Christoffel symbols of the second kind at the normal-gauge point. -/
noncomputable def kaluzaNormalGaugeChristoffel (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (M N P : Fin 4 ⊕ Unit) : ℝ :=
  ∑ Q : Fin 4 ⊕ Unit, kaluzaNormalGaugePointInverse u v d M Q *
    kaluzaNormalGaugeChristoffelFirstKind u v c k₁ k₂ d phi1 A1 Q N P

/-- Torsion-freeness at the evaluated level: symmetry in the two lower
slots. -/
theorem kaluzaNormalGaugeChristoffel_symm (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (M N P : Fin 4 ⊕ Unit) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M N P =
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M P N := by
  unfold kaluzaNormalGaugeChristoffel
  refine Finset.sum_congr rfl fun Q _ => ?_
  unfold kaluzaNormalGaugeChristoffelFirstKind
  rw [kaluzaNormalGaugeMetricJet_symm u v c k₁ k₂ d phi1 A1 Q N P]
  ring

/-- Collapse of the base-row contraction: only the diagonal inverse entry
survives. -/
theorem kaluzaNormalGaugeChristoffel_base_apply (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (mu : Fin 4) (N P : Fin 4 ⊕ Unit) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl mu) N P =
      u⁻¹ * (d mu)⁻¹ *
        kaluzaNormalGaugeChristoffelFirstKind u v c k₁ k₂ d phi1 A1
          (Sum.inl mu) N P := by
  unfold kaluzaNormalGaugeChristoffel
  rw [Fintype.sum_sum_type]
  simp [kaluzaNormalGaugePointInverse, ite_mul, zero_mul,
    Finset.sum_ite_eq]

/-- Collapse of the fiber-row contraction. -/
theorem kaluzaNormalGaugeChristoffel_fiber_apply (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (N P : Fin 4 ⊕ Unit) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ()) N P =
      v⁻¹ * kaluzaNormalGaugeChristoffelFirstKind u v c k₁ k₂ d phi1 A1
        (Sum.inr ()) N P := by
  unfold kaluzaNormalGaugeChristoffel
  rw [Fintype.sum_sum_type]
  simp [kaluzaNormalGaugePointInverse]

/-- **Base-base-base block**: the conformal-warp connection
`(k₁/2)(δ^μ_ν φ₁_ρ + δ^μ_ρ φ₁_ν - g_{νρ} φ₁^μ)`. -/
theorem kaluzaNormalGaugeChristoffel_base_base_base (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (mu nu rho : Fin 4) (hd : d mu ≠ 0) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inl mu) (Sum.inl nu) (Sum.inl rho) =
      k₁ / 2 * ((if mu = nu then phi1 rho else 0) +
        (if mu = rho then phi1 nu else 0) -
        Matrix.diagonal d nu rho * (d mu)⁻¹ * phi1 mu) := by
  rw [kaluzaNormalGaugeChristoffel_base_apply]
  simp only [kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeMetricJet, Matrix.diagonal_apply]
  rcases eq_or_ne mu nu with rfl | h1 <;> rcases eq_or_ne mu rho with rfl | h2
  · simp only [if_true]
    field_simp
  · simp only [if_true, if_neg h2, mul_zero]
    field_simp
    ring
  · simp only [if_true, if_neg h1, mul_zero]
    field_simp
    ring
  · rcases eq_or_ne nu rho with rfl | h3
    · simp only [if_true, if_neg h1, mul_zero]
      field_simp
      ring
    · simp only [if_neg h1, if_neg h2, if_neg h3, mul_zero]
      simp

/-- **Base-base-fiber block**: the Maxwell shear `(vc/2u) F_ν{}^μ`, with the
field strength appearing as the antisymmetrized gauge jet. -/
theorem kaluzaNormalGaugeChristoffel_base_base_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (mu nu : Fin 4) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inl mu) (Sum.inl nu) (Sum.inr ()) =
      v * c * u⁻¹ * (d mu)⁻¹ * (A1 nu mu - A1 mu nu) / 2 := by
  rw [kaluzaNormalGaugeChristoffel_base_apply]
  simp only [kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeMetricJet]
  ring

/-- **Base-fiber-fiber block**: the fiber-gradient force
`-(k₂v/2u) φ₁^μ`. -/
theorem kaluzaNormalGaugeChristoffel_base_fiber_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (mu : Fin 4) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inl mu) (Sum.inr ()) (Sum.inr ()) =
      -(k₂ * v * u⁻¹ * (d mu)⁻¹ * phi1 mu) / 2 := by
  rw [kaluzaNormalGaugeChristoffel_base_apply]
  simp only [kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeMetricJet]
  ring

/-- **Fiber-base-base block**: the symmetrized gauge jet
`(c/2)(∂_ν A_ρ + ∂_ρ A_ν)`. -/
theorem kaluzaNormalGaugeChristoffel_fiber_base_base (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hv : v ≠ 0) (nu rho : Fin 4) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inr ()) (Sum.inl nu) (Sum.inl rho) =
      c / 2 * (A1 nu rho + A1 rho nu) := by
  rw [kaluzaNormalGaugeChristoffel_fiber_apply]
  simp only [kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeMetricJet]
  field_simp
  ring

/-- **Fiber-base-fiber block**: the dilaton rate `(k₂/2) φ₁_ν`. -/
theorem kaluzaNormalGaugeChristoffel_fiber_base_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hv : v ≠ 0) (nu : Fin 4) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inr ()) (Sum.inl nu) (Sum.inr ()) =
      k₂ / 2 * phi1 nu := by
  rw [kaluzaNormalGaugeChristoffel_fiber_apply]
  simp only [kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeMetricJet]
  field_simp
  ring

/-- **Fiber-fiber-fiber block**: vanishes identically. -/
theorem kaluzaNormalGaugeChristoffel_fiber_fiber_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ) :
    kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inr ()) (Sum.inr ()) (Sum.inr ()) = 0 := by
  rw [kaluzaNormalGaugeChristoffel_fiber_apply]
  simp only [kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeMetricJet]
  ring

end NormalGaugeJet

section ConventionChristoffel

/-- Under the derived convention, the warp ratio in the Maxwell shear block
is exactly the EMD exponential weight: `v/u = e^{√3 φ}`.  The connection
therefore carries the same `exp(√3 φ)` that multiplies `F²` in the
convention-fixed action — the geometric origin of the Maxwell weight. -/
theorem conventionKaluzaWarpRatio (phi : ℝ) :
    kaluzaFiberWarp phi * (kaluzaBaseWarp phi)⁻¹ =
      Real.exp (Real.sqrt 3 * phi) := by
  unfold kaluzaFiberWarp kaluzaBaseWarp
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  have h1 := kaluzaWarpExponents_conformal_sum
  have h2 := kaluzaUpliftMaxwellExponent_eq_sqrt_three
  linear_combination phi * h2 - phi * h1

/-- Convention-fixed Maxwell shear block: the prefactor is the EMD weight
`e^{√3 φ}`. -/
theorem conventionKaluzaChristoffel_base_base_fiber (phi0 : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (mu nu : Fin 4) :
    kaluzaNormalGaugeChristoffel (kaluzaBaseWarp phi0)
        (kaluzaFiberWarp phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent d phi1 A1
        (Sum.inl mu) (Sum.inl nu) (Sum.inr ()) =
      Real.exp (Real.sqrt 3 * phi0) * (d mu)⁻¹ *
        (A1 nu mu - A1 mu nu) / 2 := by
  rw [kaluzaNormalGaugeChristoffel_base_base_fiber]
  unfold kaluzaGaugeNormalization
  rw [show kaluzaFiberWarp phi0 * 1 * (kaluzaBaseWarp phi0)⁻¹ *
      (d mu)⁻¹ * (A1 nu mu - A1 mu nu) / 2 =
      kaluzaFiberWarp phi0 * (kaluzaBaseWarp phi0)⁻¹ *
      ((d mu)⁻¹ * (A1 nu mu - A1 mu nu) / 2) by ring,
    conventionKaluzaWarpRatio]
  ring

/-- Convention-fixed dilaton-rate block: `Γ^5_{ν5} = (φ₁)_ν/√3`, since
`k₂/2 = 1/√3`. -/
theorem conventionKaluzaChristoffel_fiber_base_fiber (phi0 : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (nu : Fin 4) :
    kaluzaNormalGaugeChristoffel (kaluzaBaseWarp phi0)
        (kaluzaFiberWarp phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent d phi1 A1
        (Sum.inr ()) (Sum.inl nu) (Sum.inr ()) =
      (Real.sqrt 3)⁻¹ * phi1 nu := by
  rw [kaluzaNormalGaugeChristoffel_fiber_base_fiber _ _ _ _ _ _ _ _
    (kaluzaFiberWarp_ne_zero phi0)]
  unfold kaluzaFiberWarpExponent
  ring

end ConventionChristoffel

end RainichKaluza
