import RainichKaluza.LocalExteriorSeed

/-!
# Algebraic radial-gauge potential two-jets

This file records the finite-jet part of the radial homotopy formula.  In the
coordinate convention

`F i j = ∂_i A_j - ∂_j A_i`,

an alternating value `F0` and a closed alternating first jet `F1` have the
radial-gauge potential jets

`A1 i j   = (1 / 2) * F0 i j`,

`A2 k i j = (1 / 3) * (F1 k i j + F1 i k j)`.

The first two indices of `A2` are derivative directions and the last is the
one-form component.  Thus symmetry of the derivative slots is manifest.
Alternation of `F1` and the coordinate closure identity prove that
differentiating the potential curl recovers exactly `F1`.
-/

namespace RainichKaluza

open scoped Matrix
open Matrix

/-- A coordinate second derivative of a one-form: two derivative slots,
followed by the one-form component. -/
abbrev OneFormSecondDerivative4 := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- First derivative at the origin of the radial-gauge potential associated
to the two-form value `F0`. -/
noncomputable def radialGaugePotentialFirstJet4 (F0 : Matrix4) : Matrix4 :=
  (1 / 2 : ℝ) • F0

/-- Second derivative at the origin of the radial-gauge potential associated
to the two-form first jet `F1`.  The derivative slots are `k,i`; the potential
component is `j`. -/
noncomputable def radialGaugePotentialSecondJet4
    (F1 : TwoFormFirstDerivative4) : OneFormSecondDerivative4 :=
  fun k i j => (1 / 3 : ℝ) * (F1 k i j + F1 i k j)

/-- The first potential jet has curl equal to the prescribed alternating
two-form value. -/
theorem radialGaugePotentialFirstJet4_curvature
    (F0 : Matrix4) (hF0 : F0ᵀ = -F0) (i j : Fin 4) :
    radialGaugePotentialFirstJet4 F0 i j -
        radialGaugePotentialFirstJet4 F0 j i =
      F0 i j := by
  have hskew : F0 j i = -F0 i j := by
    have h := congrArg (fun M : Matrix4 => M i j) hF0
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  simp only [radialGaugePotentialFirstJet4, Matrix.smul_apply, smul_eq_mul]
  rw [hskew]
  ring

/-- The two derivative slots of the radial-gauge potential second jet
commute. -/
theorem radialGaugePotentialSecondJet4_derivative_symm
    (F1 : TwoFormFirstDerivative4) (k i j : Fin 4) :
    radialGaugePotentialSecondJet4 F1 k i j =
      radialGaugePotentialSecondJet4 F1 i k j := by
  simp only [radialGaugePotentialSecondJet4]
  rw [add_comm]

/-- If `F1` is alternating in its two-form slots and closed, the derivative
of the potential curl is exactly the prescribed two-form first jet. -/
theorem radialGaugePotentialSecondJet4_curvatureDerivative
    (F1 : TwoFormFirstDerivative4)
    (hF1 : ∀ k, (F1 k)ᵀ = -F1 k)
    (hclosed : matrixExteriorDerivative F1 = 0)
    (k i j : Fin 4) :
    radialGaugePotentialSecondJet4 F1 k i j -
        radialGaugePotentialSecondJet4 F1 k j i =
      F1 k i j := by
  have hskew (a b c : Fin 4) : F1 a b c = -F1 a c b := by
    have h := congrArg (fun M : Matrix4 => M c b) (hF1 a)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  have hcyclic : F1 k i j + F1 i j k + F1 j k i = 0 := by
    have h := congrArg (fun H : ThreeTensor4 => H k i j) hclosed
    simpa only [matrixExteriorDerivative, Pi.zero_apply] using h
  simp only [radialGaugePotentialSecondJet4]
  rw [hskew i k j, hskew k j i]
  linarith

/-- Packaged algebraic two-jet realization theorem used when passing from a
closed Maxwell first jet to a gauge-potential second jet. -/
theorem radialGaugePotentialTwoJet4_realizes
    (F0 : Matrix4) (F1 : TwoFormFirstDerivative4)
    (hF0 : F0ᵀ = -F0)
    (hF1 : ∀ k, (F1 k)ᵀ = -F1 k)
    (hclosed : matrixExteriorDerivative F1 = 0) :
    (∀ i j,
      radialGaugePotentialFirstJet4 F0 i j -
          radialGaugePotentialFirstJet4 F0 j i =
        F0 i j) ∧
    (∀ k i j,
      radialGaugePotentialSecondJet4 F1 k i j =
        radialGaugePotentialSecondJet4 F1 i k j) ∧
    (∀ k i j,
      radialGaugePotentialSecondJet4 F1 k i j -
          radialGaugePotentialSecondJet4 F1 k j i =
        F1 k i j) := by
  exact ⟨radialGaugePotentialFirstJet4_curvature F0 hF0,
    radialGaugePotentialSecondJet4_derivative_symm F1,
    radialGaugePotentialSecondJet4_curvatureDerivative F1 hF1 hclosed⟩

end RainichKaluza
