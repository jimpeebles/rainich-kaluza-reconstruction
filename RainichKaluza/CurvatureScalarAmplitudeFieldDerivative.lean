import RainichKaluza.SmoothCurvatureProjector
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Derivatives of curvature-reconstructed scalar amplitudes

This file differentiates the genuine scalar fields obtained by applying the
signature-adjusted square root to the two reconstructed spectral diagonals.
It identifies their Frechet derivatives with the evaluated rational formulas
already used by the curvature branch jet.
-/

namespace RainichKaluza

open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The first reconstructed scalar diagonal as a genuine field. -/
noncomputable def reconstructedDiagonalAField
    (a b qSq : X → ℝ) (z : X) : ℝ :=
  reconstructedDiagonalA (a z) (b z) (qSq z)

/-- The second reconstructed scalar diagonal as a genuine field. -/
noncomputable def reconstructedDiagonalBField
    (a b qSq : X → ℝ) (z : X) : ℝ :=
  reconstructedDiagonalB (a z) (b z) (qSq z)

/-- Positive square-root representative of the first scalar amplitude. -/
noncomputable def reconstructedScalarAmplitudeA
    (epsilon : ℝ) (a b qSq : X → ℝ) (z : X) : ℝ :=
  smoothScalarAmplitude epsilon (reconstructedDiagonalAField a b qSq) z

/-- Positive square-root representative of the second scalar amplitude. -/
noncomputable def reconstructedScalarAmplitudeB
    (epsilon : ℝ) (a b qSq : X → ℝ) (z : X) : ℝ :=
  smoothScalarAmplitude epsilon (reconstructedDiagonalBField a b qSq) z

theorem differentiableAt_reconstructedDiagonalAField
    (a b qSq : X → ℝ) (z : X)
    (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z)
    (hqSq : DifferentiableAt ℝ qSq z)
    (hab : a z ≠ b z) :
    DifferentiableAt ℝ (reconstructedDiagonalAField a b qSq) z := by
  unfold reconstructedDiagonalAField reconstructedDiagonalA
  exact ((ha.pow 2).sub hqSq).mul
    ((ha.sub hb).inv (sub_ne_zero.mpr hab))

theorem differentiableAt_reconstructedDiagonalBField
    (a b qSq : X → ℝ) (z : X)
    (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z)
    (hqSq : DifferentiableAt ℝ qSq z)
    (hab : a z ≠ b z) :
    DifferentiableAt ℝ (reconstructedDiagonalBField a b qSq) z := by
  unfold reconstructedDiagonalBField reconstructedDiagonalB
  exact ((hb.pow 2).sub hqSq).mul
    ((hb.sub ha).inv (sub_ne_zero.mpr hab.symm))

/-- Exact derivative of a signature-adjusted positive square-root amplitude. -/
theorem smoothScalarAmplitude_fderiv_apply
    (epsilon : ℝ) (u : X → ℝ) (z w : X)
    (hu : DifferentiableAt ℝ u z)
    (hpos : 0 < 2 * epsilon * u z) :
    fderiv ℝ (smoothScalarAmplitude epsilon u) z w =
      scalarAmplitudeDerivative epsilon (smoothScalarAmplitude epsilon u z)
        (fderiv ℝ u z w) := by
  have harg : DifferentiableAt ℝ (fun q => 2 * epsilon * u q) z :=
    hu.const_mul (2 * epsilon)
  have harg0 : 2 * epsilon * u z ≠ 0 := ne_of_gt hpos
  change fderiv ℝ (fun q => Real.sqrt (2 * epsilon * u q)) z w = _
  rw [fderiv_sqrt harg harg0]
  rw [fderiv_const_mul hu (2 * epsilon)]
  simp only [smul_apply]
  unfold smoothScalarAmplitude scalarAmplitudeDerivative
  have hsqrt0 : Real.sqrt (2 * epsilon * u z) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hpos
  ring_nf

/-- The first reconstructed diagonal field has the displayed rational
Frechet derivative. -/
theorem reconstructedDiagonalAField_fderiv_apply
    (a b qSq : X → ℝ) (z w : X)
    (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z)
    (hqSq : DifferentiableAt ℝ qSq z)
    (hab : a z ≠ b z) :
    fderiv ℝ (reconstructedDiagonalAField a b qSq) z w =
      reconstructedDiagonalADerivative (a z) (b z) (qSq z)
        (fderiv ℝ a z w) (fderiv ℝ b z w) (fderiv ℝ qSq z w) := by
  have hnum : DifferentiableAt ℝ (fun q => a q * a q - qSq q) z :=
    (ha.mul ha).sub hqSq
  have hden : DifferentiableAt ℝ (fun q => a q - b q) z := ha.sub hb
  have hden0 : a z - b z ≠ 0 := sub_ne_zero.mpr hab
  have hinv := hden.inv hden0
  unfold reconstructedDiagonalAField reconstructedDiagonalA
  simp only [pow_two, div_eq_mul_inv]
  change (fderiv ℝ (fun q =>
    (a q * a q - qSq q) * ((fun r => a r - b r)⁻¹) q) z) w = _
  rw [fderiv_fun_mul hnum hinv]
  have haa : fderiv ℝ (fun q => a q * a q) z =
      a z • fderiv ℝ a z + a z • fderiv ℝ a z := by
    exact fderiv_fun_mul ha ha
  have hnumF : fderiv ℝ (fun q => a q * a q - qSq q) z =
      fderiv ℝ (fun q => a q * a q) z - fderiv ℝ qSq z := by
    exact fderiv_fun_sub (ha.mul ha) hqSq
  have hcomp := fderiv_comp (f := fun q => a q - b q)
    (g := Inv.inv) (x := z) (differentiableAt_inv hden0) hden
  have hdenF : fderiv ℝ (fun q => a q - b q) z =
      fderiv ℝ a z - fderiv ℝ b z := fderiv_fun_sub ha hb
  have hinvF : fderiv ℝ (fun q => (a q - b q)⁻¹) z =
      (-(ContinuousLinearMap.mulLeftRight ℝ ℝ
        (a z - b z)⁻¹ (a z - b z)⁻¹)).comp
          (fderiv ℝ (fun q => a q - b q) z) := by
    change fderiv ℝ (Inv.inv ∘ fun q => a q - b q) z = _
    rw [hcomp, fderiv_inv' hden0]
  have hinvF' : fderiv ℝ ((fun q => a q - b q)⁻¹) z =
      (-(ContinuousLinearMap.mulLeftRight ℝ ℝ
        (a z - b z)⁻¹ (a z - b z)⁻¹)).comp
          (fderiv ℝ (fun q => a q - b q) z) := by
    change fderiv ℝ (fun q => (a q - b q)⁻¹) z = _
    exact hinvF
  rw [hnumF, haa, hinvF', hdenF]
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply, smul_apply]
  simp
  unfold reconstructedDiagonalADerivative
  field_simp [hden0]
  ring

/-- The second reconstructed diagonal field has the displayed rational
Frechet derivative. -/
theorem reconstructedDiagonalBField_fderiv_apply
    (a b qSq : X → ℝ) (z w : X)
    (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z)
    (hqSq : DifferentiableAt ℝ qSq z)
    (hab : a z ≠ b z) :
    fderiv ℝ (reconstructedDiagonalBField a b qSq) z w =
      reconstructedDiagonalBDerivative (a z) (b z) (qSq z)
        (fderiv ℝ a z w) (fderiv ℝ b z w) (fderiv ℝ qSq z w) := by
  have hnum : DifferentiableAt ℝ (fun q => b q * b q - qSq q) z :=
    (hb.mul hb).sub hqSq
  have hden : DifferentiableAt ℝ (fun q => b q - a q) z := hb.sub ha
  have hden0 : b z - a z ≠ 0 := sub_ne_zero.mpr hab.symm
  have hinv := hden.inv hden0
  unfold reconstructedDiagonalBField reconstructedDiagonalB
  simp only [pow_two, div_eq_mul_inv]
  change (fderiv ℝ (fun q =>
    (b q * b q - qSq q) * ((fun r => b r - a r)⁻¹) q) z) w = _
  rw [fderiv_fun_mul hnum hinv]
  have hbb : fderiv ℝ (fun q => b q * b q) z =
      b z • fderiv ℝ b z + b z • fderiv ℝ b z := by
    exact fderiv_fun_mul hb hb
  have hnumF : fderiv ℝ (fun q => b q * b q - qSq q) z =
      fderiv ℝ (fun q => b q * b q) z - fderiv ℝ qSq z := by
    exact fderiv_fun_sub (hb.mul hb) hqSq
  have hcomp := fderiv_comp (f := fun q => b q - a q)
    (g := Inv.inv) (x := z) (differentiableAt_inv hden0) hden
  have hdenF : fderiv ℝ (fun q => b q - a q) z =
      fderiv ℝ b z - fderiv ℝ a z := fderiv_fun_sub hb ha
  have hinvF : fderiv ℝ (fun q => (b q - a q)⁻¹) z =
      (-(ContinuousLinearMap.mulLeftRight ℝ ℝ
        (b z - a z)⁻¹ (b z - a z)⁻¹)).comp
          (fderiv ℝ (fun q => b q - a q) z) := by
    change fderiv ℝ (Inv.inv ∘ fun q => b q - a q) z = _
    rw [hcomp, fderiv_inv' hden0]
  have hinvF' : fderiv ℝ ((fun q => b q - a q)⁻¹) z =
      (-(ContinuousLinearMap.mulLeftRight ℝ ℝ
        (b z - a z)⁻¹ (b z - a z)⁻¹)).comp
          (fderiv ℝ (fun q => b q - a q) z) := by
    change fderiv ℝ (fun q => (b q - a q)⁻¹) z = _
    exact hinvF
  rw [hnumF, hbb, hinvF', hdenF]
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply, smul_apply]
  simp
  unfold reconstructedDiagonalBDerivative
  field_simp [hden0]
  ring

/-- The genuine first square-root amplitude field has exactly the curvature-
reconstructed directional derivative. -/
theorem reconstructedScalarAmplitudeA_fderiv_apply
    (epsilon : ℝ) (a b qSq : X → ℝ) (z w : X)
    (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z)
    (hqSq : DifferentiableAt ℝ qSq z)
    (hab : a z ≠ b z)
    (hpos : 0 < 2 * epsilon * reconstructedDiagonalAField a b qSq z) :
    fderiv ℝ (reconstructedScalarAmplitudeA epsilon a b qSq) z w =
      reconstructedAmplitudeADerivative epsilon
        (reconstructedScalarAmplitudeA epsilon a b qSq z)
        (a z) (b z) (qSq z)
        (fderiv ℝ a z w) (fderiv ℝ b z w) (fderiv ℝ qSq z w) := by
  have hdiag := differentiableAt_reconstructedDiagonalAField
    a b qSq z ha hb hqSq hab
  unfold reconstructedScalarAmplitudeA
  rw [smoothScalarAmplitude_fderiv_apply epsilon
    (reconstructedDiagonalAField a b qSq) z w hdiag hpos]
  rw [reconstructedDiagonalAField_fderiv_apply a b qSq z w ha hb hqSq hab]
  rfl

/-- The genuine second square-root amplitude field has exactly the curvature-
reconstructed directional derivative. -/
theorem reconstructedScalarAmplitudeB_fderiv_apply
    (epsilon : ℝ) (a b qSq : X → ℝ) (z w : X)
    (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z)
    (hqSq : DifferentiableAt ℝ qSq z)
    (hab : a z ≠ b z)
    (hpos : 0 < 2 * epsilon * reconstructedDiagonalBField a b qSq z) :
    fderiv ℝ (reconstructedScalarAmplitudeB epsilon a b qSq) z w =
      reconstructedAmplitudeBDerivative epsilon
        (reconstructedScalarAmplitudeB epsilon a b qSq z)
        (a z) (b z) (qSq z)
        (fderiv ℝ a z w) (fderiv ℝ b z w) (fderiv ℝ qSq z w) := by
  have hdiag := differentiableAt_reconstructedDiagonalBField
    a b qSq z ha hb hqSq hab
  unfold reconstructedScalarAmplitudeB
  rw [smoothScalarAmplitude_fderiv_apply epsilon
    (reconstructedDiagonalBField a b qSq) z w hdiag hpos]
  rw [reconstructedDiagonalBField_fderiv_apply a b qSq z w ha hb hqSq hab]
  rfl

/-- The first reconstructed amplitude is `C^n` on its noncollision,
positive-radicand patch. -/
theorem contDiffOn_reconstructedScalarAmplitudeA
    {n : WithTop ℕ∞} {U : Set X} (epsilon : ℝ) {a b qSq : X → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U)
    (hqSq : ContDiffOn ℝ n qSq U)
    (hab : ∀ z ∈ U, a z ≠ b z)
    (hpos : ∀ z ∈ U,
      0 < 2 * epsilon * reconstructedDiagonalAField a b qSq z) :
    ContDiffOn ℝ n (reconstructedScalarAmplitudeA epsilon a b qSq) U := by
  unfold reconstructedScalarAmplitudeA
  apply contDiffOn_smoothScalarAmplitude epsilon
  · change ContDiffOn ℝ n
      (fun z => reconstructedDiagonalA (a z) (b z) (qSq z)) U
    exact contDiffOn_reconstructedDiagonalA ha hb hqSq hab
  · exact hpos

/-- The second reconstructed amplitude is `C^n` on its noncollision,
positive-radicand patch. -/
theorem contDiffOn_reconstructedScalarAmplitudeB
    {n : WithTop ℕ∞} {U : Set X} (epsilon : ℝ) {a b qSq : X → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U)
    (hqSq : ContDiffOn ℝ n qSq U)
    (hab : ∀ z ∈ U, a z ≠ b z)
    (hpos : ∀ z ∈ U,
      0 < 2 * epsilon * reconstructedDiagonalBField a b qSq z) :
    ContDiffOn ℝ n (reconstructedScalarAmplitudeB epsilon a b qSq) U := by
  unfold reconstructedScalarAmplitudeB
  apply contDiffOn_smoothScalarAmplitude epsilon
  · change ContDiffOn ℝ n
      (fun z => reconstructedDiagonalB (a z) (b z) (qSq z)) U
    exact contDiffOn_reconstructedDiagonalB ha hb hqSq hab
  · exact hpos

end RainichKaluza
