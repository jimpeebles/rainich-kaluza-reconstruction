import RainichKaluza.UpliftConvention
import RainichKaluza.LorentzFrameTransport
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Kaluza block-metric assembly: congruence, inverse, and determinant

Phase IV.3 items one and three, in the coordinate matrix layer.  The
five-dimensional index set is `Fin 4 ⊕ Unit`: the base directions and the
circle direction.

The central observation is structural: the Kaluza block metric *is* the
unipotent congruence transform

`ĝ = Pᵀ (u·g ⊕ v) P`,   `P = [[1, 0], [c·Aᵀ, 1]]`,

of the block-diagonal core.  Taking this as the definition makes symmetry,
the explicit `fromBlocks` entry formulas, the explicit inverse-metric
formulas, and the determinant

`det ĝ = u⁴ · v · det g`

exact matrix algebra.  Because `P` is unipotent, the congruence also settles
the signature question at this level: `ĝ` is congruent to `u·g ⊕ v`, so for
positive warp factors the index of `ĝ` is the index of `g`.  The companion
pairing-level theorem `kaluzaMetricPairing_lift_orthogonal` realizes the same
statement for the abstract evaluation layer by exhibiting the explicit lifted
pseudo-orthogonal family.

The convention-fixed instantiations at the derived warp factors
`u = exp(c₁φ)`, `v = exp(c₂φ)`, `c = 1` follow at the end; in particular
`det ĝ < 0 ↔ det g < 0`, the determinant form of Lorentz-signature
preservation.
-/

namespace RainichKaluza

open Matrix

/-- Five-dimensional coordinate matrices: four base directions plus the
circle direction. -/
abbrev Matrix5 := Matrix (Fin 4 ⊕ Unit) (Fin 4 ⊕ Unit) ℝ

/-- A one-form as a column matrix. -/
def oneFormColumn (A : OneForm4) : Matrix (Fin 4) Unit ℝ :=
  Matrix.of fun i _ => A i

/-- A one-form as a row matrix. -/
def oneFormRow (A : OneForm4) : Matrix Unit (Fin 4) ℝ :=
  Matrix.of fun _ j => A j

@[simp] theorem oneFormColumn_transpose (A : OneForm4) :
    (oneFormColumn A)ᵀ = oneFormRow A := rfl

@[simp] theorem oneFormRow_transpose (A : OneForm4) :
    (oneFormRow A)ᵀ = oneFormColumn A := rfl

/-- The unipotent fiber shear `P`: identity on the base block, identity on
the fiber, and the gauge row `c·Aᵀ` mixing base directions into the fiber
component. -/
def kaluzaShear (c : ℝ) (A : OneForm4) : Matrix5 :=
  Matrix.fromBlocks 1 0 (c • oneFormRow A) 1

/-- Inverse shear: negate the gauge row. -/
def kaluzaShearInverse (c : ℝ) (A : OneForm4) : Matrix5 :=
  Matrix.fromBlocks 1 0 (-(c • oneFormRow A)) 1

/-- The block-diagonal core `u·g ⊕ v` of the warped metric. -/
def kaluzaCore (u v : ℝ) (g : Matrix4) : Matrix5 :=
  Matrix.fromBlocks (u • g) 0 0 (v • (1 : Matrix Unit Unit ℝ))

/-- **The assembled Kaluza block metric**, defined as the unipotent
congruence transform of the core.  The entry formulas are recovered in
`kaluzaBlockMetric_eq_fromBlocks`. -/
def kaluzaBlockMetric (u v c : ℝ) (g : Matrix4) (A : OneForm4) : Matrix5 :=
  (kaluzaShear c A)ᵀ * kaluzaCore u v g * kaluzaShear c A

theorem kaluzaShear_mul_inverse (c : ℝ) (A : OneForm4) :
    kaluzaShear c A * kaluzaShearInverse c A = 1 := by
  unfold kaluzaShear kaluzaShearInverse
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem kaluzaShearInverse_mul (c : ℝ) (A : OneForm4) :
    kaluzaShearInverse c A * kaluzaShear c A = 1 := by
  unfold kaluzaShear kaluzaShearInverse
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

/-- Entry form of the block metric: exactly the classical Kaluza ansatz
`ĝ_{μν} = u g_{μν} + v c² A_μ A_ν`, `ĝ_{μ5} = v c A_μ`, `ĝ_{55} = v`. -/
theorem kaluzaBlockMetric_eq_fromBlocks (u v c : ℝ) (g : Matrix4)
    (A : OneForm4) :
    kaluzaBlockMetric u v c g A =
      Matrix.fromBlocks
        (u • g + (v * c * c) • (oneFormColumn A * oneFormRow A))
        ((v * c) • oneFormColumn A)
        ((v * c) • oneFormRow A)
        (v • (1 : Matrix Unit Unit ℝ)) := by
  unfold kaluzaBlockMetric kaluzaShear kaluzaCore
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    mul_comm]

/-- The block metric is symmetric whenever the base metric is symmetric. -/
theorem kaluzaBlockMetric_transpose (u v c : ℝ) (g : Matrix4)
    (A : OneForm4) (hg : gᵀ = g) :
    (kaluzaBlockMetric u v c g A)ᵀ = kaluzaBlockMetric u v c g A := by
  unfold kaluzaBlockMetric kaluzaCore
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_smul, hg, Matrix.transpose_zero,
    Matrix.transpose_one]
  rw [Matrix.mul_assoc]

/-- **Explicit inverse of the Kaluza block metric**, assembled from the
inverse shear and the inverse core. -/
noncomputable def kaluzaBlockMetricInverse (u v c : ℝ) (ginv : Matrix4)
    (A : OneForm4) : Matrix5 :=
  kaluzaShearInverse c A *
    Matrix.fromBlocks (u⁻¹ • ginv) 0 0 (v⁻¹ • (1 : Matrix Unit Unit ℝ)) *
    (kaluzaShearInverse c A)ᵀ

/-- Entry form of the inverse: the classical formulas
`ĝ^{μν} = u⁻¹ g^{μν}`, `ĝ^{μ5} = -u⁻¹ c (g⁻¹A)^μ`,
`ĝ^{55} = v⁻¹ + u⁻¹ c² A·g⁻¹A`. -/
theorem kaluzaBlockMetricInverse_eq_fromBlocks (u v c : ℝ)
    (ginv : Matrix4) (A : OneForm4) :
    kaluzaBlockMetricInverse u v c ginv A =
      Matrix.fromBlocks
        (u⁻¹ • ginv)
        (-(u⁻¹ * c) • (ginv * oneFormColumn A))
        (-(u⁻¹ * c) • (oneFormRow A * ginv))
        (v⁻¹ • (1 : Matrix Unit Unit ℝ) +
          (u⁻¹ * c * c) • (oneFormRow A * ginv * oneFormColumn A)) := by
  unfold kaluzaBlockMetricInverse kaluzaShearInverse
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.mul_assoc, mul_comm, neg_smul, Matrix.neg_mul,
    Matrix.mul_neg, add_comm]

/-- The core and inverse core multiply to the identity when the warp factors
are nonzero and `ginv` is a right inverse of `g`. -/
theorem kaluzaCore_mul_inverse (u v : ℝ) (g ginv : Matrix4)
    (hu : u ≠ 0) (hv : v ≠ 0) (hg : g * ginv = 1) :
    kaluzaCore u v g *
      Matrix.fromBlocks (u⁻¹ • ginv) 0 0
        (v⁻¹ • (1 : Matrix Unit Unit ℝ)) = 1 := by
  unfold kaluzaCore
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hg,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add,
    smul_zero]
  rw [inv_mul_cancel₀ hu, inv_mul_cancel₀ hv, one_smul, one_smul,
    Matrix.fromBlocks_one]

/-- The Kaluza block metric and its assembled inverse are two-sided
inverses. -/
theorem kaluzaBlockMetric_mul_inverse (u v c : ℝ) (g ginv : Matrix4)
    (A : OneForm4) (hu : u ≠ 0) (hv : v ≠ 0) (hg : g * ginv = 1) :
    kaluzaBlockMetric u v c g A *
      kaluzaBlockMetricInverse u v c ginv A = 1 := by
  unfold kaluzaBlockMetric kaluzaBlockMetricInverse
  have hcore := kaluzaCore_mul_inverse u v g ginv hu hv hg
  calc (kaluzaShear c A)ᵀ * kaluzaCore u v g * kaluzaShear c A *
        (kaluzaShearInverse c A *
          Matrix.fromBlocks (u⁻¹ • ginv) 0 0
            (v⁻¹ • (1 : Matrix Unit Unit ℝ)) *
          (kaluzaShearInverse c A)ᵀ) =
      (kaluzaShear c A)ᵀ * kaluzaCore u v g *
        (kaluzaShear c A * kaluzaShearInverse c A) *
        (Matrix.fromBlocks (u⁻¹ • ginv) 0 0
          (v⁻¹ • (1 : Matrix Unit Unit ℝ)) *
          (kaluzaShearInverse c A)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = (kaluzaShear c A)ᵀ *
        (kaluzaCore u v g *
          Matrix.fromBlocks (u⁻¹ • ginv) 0 0
            (v⁻¹ • (1 : Matrix Unit Unit ℝ))) *
        (kaluzaShearInverse c A)ᵀ := by
        rw [kaluzaShear_mul_inverse]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (kaluzaShear c A)ᵀ * (kaluzaShearInverse c A)ᵀ := by
        rw [hcore]
        simp only [Matrix.mul_one]
    _ = (kaluzaShearInverse c A * kaluzaShear c A)ᵀ := by
        rw [Matrix.transpose_mul]
    _ = 1 := by rw [kaluzaShearInverse_mul, Matrix.transpose_one]

/-- Reverse composition, from a left inverse of the base metric. -/
theorem kaluzaBlockMetricInverse_mul (u v c : ℝ) (g ginv : Matrix4)
    (A : OneForm4) (hu : u ≠ 0) (hv : v ≠ 0) (hg : ginv * g = 1) :
    kaluzaBlockMetricInverse u v c ginv A *
      kaluzaBlockMetric u v c g A = 1 := by
  unfold kaluzaBlockMetric kaluzaBlockMetricInverse
  have hcore : Matrix.fromBlocks (u⁻¹ • ginv) 0 0
      (v⁻¹ • (1 : Matrix Unit Unit ℝ)) * kaluzaCore u v g = 1 := by
    unfold kaluzaCore
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hg,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add,
      smul_zero]
    rw [mul_inv_cancel₀ hu, mul_inv_cancel₀ hv, one_smul, one_smul,
      Matrix.fromBlocks_one]
  calc kaluzaShearInverse c A *
        Matrix.fromBlocks (u⁻¹ • ginv) 0 0
          (v⁻¹ • (1 : Matrix Unit Unit ℝ)) *
        (kaluzaShearInverse c A)ᵀ *
        ((kaluzaShear c A)ᵀ * kaluzaCore u v g * kaluzaShear c A) =
      kaluzaShearInverse c A *
        Matrix.fromBlocks (u⁻¹ • ginv) 0 0
          (v⁻¹ • (1 : Matrix Unit Unit ℝ)) *
        ((kaluzaShearInverse c A)ᵀ * (kaluzaShear c A)ᵀ) *
        (kaluzaCore u v g * kaluzaShear c A) := by
        simp only [Matrix.mul_assoc]
    _ = kaluzaShearInverse c A *
        (Matrix.fromBlocks (u⁻¹ • ginv) 0 0
          (v⁻¹ • (1 : Matrix Unit Unit ℝ)) *
          kaluzaCore u v g) * kaluzaShear c A := by
        rw [← Matrix.transpose_mul, kaluzaShear_mul_inverse,
          Matrix.transpose_one]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = kaluzaShearInverse c A * kaluzaShear c A := by
        rw [hcore]
        simp only [Matrix.mul_one]
    _ = 1 := kaluzaShearInverse_mul c A

/-- The shear is unipotent: determinant one. -/
theorem kaluzaShear_det (c : ℝ) (A : OneForm4) :
    (kaluzaShear c A).det = 1 := by
  unfold kaluzaShear
  rw [Matrix.det_fromBlocks_zero₁₂]
  simp

/-- **Determinant of the Kaluza block metric**: `det ĝ = u⁴ · v · det g`.
For positive warp factors the sign of `det ĝ` is the sign of `det g`; a
Lorentzian base has `det g < 0`, hence `det ĝ < 0`, the determinant
consistency condition for signature `(-,+,+,+,+)`. -/
theorem kaluzaBlockMetric_det (u v c : ℝ) (g : Matrix4) (A : OneForm4) :
    (kaluzaBlockMetric u v c g A).det = u ^ 4 * v * g.det := by
  unfold kaluzaBlockMetric kaluzaCore
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    kaluzaShear_det, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul,
    Matrix.det_smul]
  simp [Fintype.card_fin, mul_comm, mul_assoc]

section PairingLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fiber component of the pseudo-orthogonal lift of a base vector: the
compensating shift `-c·A(X)` that kills the cross term. -/
def kaluzaLiftFiber (c : ℝ) (A : E →L[ℝ] ℝ) (X : E) : ℝ :=
  -(c * A X)

/-- Lifted base vectors pair through the base metric alone: the fiber shift
removes every gauge cross term. -/
theorem kaluzaMetricPairing_lift_lift (u v c : ℝ)
    (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ) (X Y : E) :
    kaluzaMetricPairing u v c g A X Y
      (kaluzaLiftFiber c A X) (kaluzaLiftFiber c A Y) = u * g X Y := by
  unfold kaluzaMetricPairing kaluzaFiberOneForm kaluzaLiftFiber
  ring

/-- A lifted base vector is orthogonal to the pure fiber vector `(0, 1)`. -/
theorem kaluzaMetricPairing_lift_fiber (u v c : ℝ)
    (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ) (X : E) :
    kaluzaMetricPairing u v c g A X 0
      (kaluzaLiftFiber c A X) 1 = 0 := by
  unfold kaluzaMetricPairing kaluzaFiberOneForm kaluzaLiftFiber
  simp

/-- The pure fiber vector has squared length `v`. -/
theorem kaluzaMetricPairing_fiber_fiber (u v c : ℝ)
    (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ) :
    kaluzaMetricPairing u v c g A 0 0 1 1 = v := by
  unfold kaluzaMetricPairing kaluzaFiberOneForm
  simp

/-- **Signature lift.** A `g`-orthogonal family with diagonal values
`eps i`, lifted by the compensating fiber shifts and extended by the pure
fiber vector, is `ĝ`-orthogonal with diagonal values `(u·eps i, v)`.  For
`u, v > 0` and a Lorentzian family `eps = (-1,1,1,1)` this exhibits an
index-one five-dimensional pseudo-orthogonal family: the assembled metric
has signature `(-,+,+,+,+)`. -/
theorem kaluzaMetricPairing_lift_orthogonal (u v c : ℝ)
    (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (e : Fin 4 → E) (eps : Fin 4 → ℝ)
    (horth : ∀ i j, g (e i) (e j) = if i = j then eps i else 0) :
    (∀ i j, kaluzaMetricPairing u v c g A (e i) (e j)
        (kaluzaLiftFiber c A (e i)) (kaluzaLiftFiber c A (e j)) =
      if i = j then u * eps i else 0) ∧
    (∀ i, kaluzaMetricPairing u v c g A (e i) 0
        (kaluzaLiftFiber c A (e i)) 1 = 0) ∧
    kaluzaMetricPairing u v c g A 0 0 1 1 = v := by
  refine ⟨fun i j => ?_, fun i => kaluzaMetricPairing_lift_fiber u v c g A
    (e i), kaluzaMetricPairing_fiber_fiber u v c g A⟩
  rw [kaluzaMetricPairing_lift_lift, horth i j]
  by_cases h : i = j <;> simp [h]

end PairingLift

section ConventionInstances

/-- Convention-fixed block metric at the derived warp factors. -/
noncomputable def conventionKaluzaBlockMetric
    (phi : ℝ) (g : Matrix4) (A : OneForm4) : Matrix5 :=
  kaluzaBlockMetric (kaluzaBaseWarp phi) (kaluzaFiberWarp phi)
    kaluzaGaugeNormalization g A

/-- Convention-fixed inverse block metric. -/
noncomputable def conventionKaluzaBlockMetricInverse
    (phi : ℝ) (ginv : Matrix4) (A : OneForm4) : Matrix5 :=
  kaluzaBlockMetricInverse (kaluzaBaseWarp phi) (kaluzaFiberWarp phi)
    kaluzaGaugeNormalization ginv A

theorem conventionKaluzaBlockMetric_mul_inverse
    (phi : ℝ) (g ginv : Matrix4) (A : OneForm4) (hg : g * ginv = 1) :
    conventionKaluzaBlockMetric phi g A *
      conventionKaluzaBlockMetricInverse phi ginv A = 1 :=
  kaluzaBlockMetric_mul_inverse _ _ _ g ginv A
    (kaluzaBaseWarp_ne_zero phi) (kaluzaFiberWarp_ne_zero phi) hg

theorem conventionKaluzaBlockMetricInverse_mul
    (phi : ℝ) (g ginv : Matrix4) (A : OneForm4) (hg : ginv * g = 1) :
    conventionKaluzaBlockMetricInverse phi ginv A *
      conventionKaluzaBlockMetric phi g A = 1 :=
  kaluzaBlockMetricInverse_mul _ _ _ g ginv A
    (kaluzaBaseWarp_ne_zero phi) (kaluzaFiberWarp_ne_zero phi) hg

/-- **Lorentz-determinant preservation** at the derived convention: the
five-dimensional determinant is negative exactly when the four-dimensional
determinant is negative. -/
theorem conventionKaluzaBlockMetric_det_neg_iff
    (phi : ℝ) (g : Matrix4) (A : OneForm4) :
    (conventionKaluzaBlockMetric phi g A).det < 0 ↔ g.det < 0 := by
  unfold conventionKaluzaBlockMetric
  rw [kaluzaBlockMetric_det]
  constructor
  · intro h
    by_contra hge
    have hge' : 0 ≤ g.det := not_lt.mp hge
    have hpos : 0 < kaluzaBaseWarp phi ^ 4 * kaluzaFiberWarp phi :=
      mul_pos (pow_pos (kaluzaBaseWarp_pos phi) 4) (kaluzaFiberWarp_pos phi)
    nlinarith
  · intro h
    have hpos : 0 < kaluzaBaseWarp phi ^ 4 * kaluzaFiberWarp phi :=
      mul_pos (pow_pos (kaluzaBaseWarp_pos phi) 4) (kaluzaFiberWarp_pos phi)
    calc kaluzaBaseWarp phi ^ 4 * kaluzaFiberWarp phi * g.det
        = (kaluzaBaseWarp phi ^ 4 * kaluzaFiberWarp phi) * g.det := by ring
      _ < 0 := mul_neg_of_pos_of_neg hpos h

end ConventionInstances

end RainichKaluza
