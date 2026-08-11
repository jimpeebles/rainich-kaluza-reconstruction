import RainichKaluza.TransportedSeedDerivative
import RainichKaluza.ExteriorComplexion
import Mathlib.Tactic.Module

/-!
# Local exterior derivative of the reconstructed Maxwell seed

This file instantiates the abstract exterior-complexion algebra in an oriented
four-dimensional coordinate trivialization.  The local orthonormal coframe
orientation is chosen to agree with the spacetime orientation, so transporting
the canonical Hodge seed gives the geometric Hodge partner.  A first
derivative of a two-form is
represented by four directional derivative matrices and exteriorized by
cyclic antisymmetrization.  Applying this construction to the transported
positive-`q` seed and its Hodge partner produces the actual seed-channel
three-forms appearing in the EMD closure test.

The input jets `dL` and `dq` are supplied chart derivatives.  The smoothness
theorems in `SmoothMaxwellSeed` guarantee their local existence; the spectral
projector derivative results describe how curvature derivatives determine
the varying principal planes.
-/

namespace RainichKaluza

open scoped Matrix
open Matrix

/-- Coordinate one-forms in a four-dimensional local trivialization. -/
abbrev OneForm4 := Fin 4 → ℝ

/-- Coordinate covariant three-tensors.  The constructors below prove the
alternation properties needed for the tensors they produce. -/
abbrev ThreeTensor4 := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- A first derivative of a matrix two-form, indexed by derivative direction. -/
abbrev TwoFormFirstDerivative4 := Fin 4 → Matrix4

/-- Coordinate exterior derivative of a two-form first jet. -/
def matrixExteriorDerivative
    (D : TwoFormFirstDerivative4) : ThreeTensor4 :=
  fun k i j => D k i j + D i j k + D j k i

/-- Coordinate wedge product of a one-form and a two-form. -/
def matrixOneWedgeTwoTensor
    (v : OneForm4) (F : Matrix4) : ThreeTensor4 :=
  fun k i j => v k * F i j + v i * F j k + v j * F k i

/-- The coordinate wedge product as the bilinear map expected by the
exterior-complexion theorem. -/
def matrixOneWedgeTwo :
    OneWedgeTwo OneForm4 Matrix4 ThreeTensor4 where
  toFun v :=
    { toFun := matrixOneWedgeTwoTensor v
      map_add' := by
        intro F H
        ext k i j
        simp [matrixOneWedgeTwoTensor]
        ring
      map_smul' := by
        intro c F
        ext k i j
        simp [matrixOneWedgeTwoTensor]
        ring }
  map_add' := by
    intro v w
    ext F k i j
    simp [matrixOneWedgeTwoTensor]
    ring
  map_smul' := by
    intro c v
    ext F k i j
    simp [matrixOneWedgeTwoTensor]
    ring

/-- A coordinate three-tensor is alternating when either adjacent swap
changes its sign. -/
def IsAlternatingThreeTensor (H : ThreeTensor4) : Prop :=
  (∀ k i j, H i k j = -H k i j) ∧
    ∀ k i j, H k j i = -H k i j

/-- Exteriorizing a first derivative of skew matrices produces an
alternating three-tensor. -/
theorem matrixExteriorDerivative_alternating
    (D : TwoFormFirstDerivative4)
    (hD : ∀ k, (D k)ᵀ = -D k) :
    IsAlternatingThreeTensor (matrixExteriorDerivative D) := by
  have hskew (k i j : Fin 4) : D k i j = -D k j i := by
    have h := congrArg (fun M : Matrix4 => M j i) (hD k)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  constructor
  · intro k i j
    simp only [matrixExteriorDerivative]
    rw [hskew i k j, hskew k j i, hskew j i k]
    ring
  · intro k i j
    simp only [matrixExteriorDerivative]
    rw [hskew k j i, hskew j i k, hskew i k j]
    ring

/-- Wedging a one-form with a skew matrix produces an alternating
three-tensor. -/
theorem matrixOneWedgeTwoTensor_alternating
    (v : OneForm4) (F : Matrix4) (hF : Fᵀ = -F) :
    IsAlternatingThreeTensor (matrixOneWedgeTwoTensor v F) := by
  have hskew (i j : Fin 4) : F i j = -F j i := by
    have h := congrArg (fun M : Matrix4 => M j i) hF
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  constructor
  · intro k i j
    simp only [matrixOneWedgeTwoTensor]
    rw [hskew k j, hskew j i, hskew i k]
    ring
  · intro k i j
    simp only [matrixOneWedgeTwoTensor]
    rw [hskew j i, hskew i k, hskew k j]
    ring

/-- Transported Hodge partner of the canonical positive-`q` seed, in the
orientation selected by the local Lorentz coframe. -/
noncomputable def transportedPositiveQHodgeSeed
    (L : Matrix4) (q : ℝ) : Matrix4 :=
  transportTwoForm L
    (canonicalHodgeStar (Real.sqrt (2 * q)) 0)

/-- Canonical first derivative of the positive-`q` Hodge seed. -/
noncomputable def canonicalPositiveQHodgeSeedDerivative
    (q dq : ℝ) : Matrix4 :=
  canonicalHodgeStar (canonicalPositiveQAmplitudeDerivative q dq) 0

/-- The Hodge-seed derivative has the same logarithmic amplitude as the
electric seed. -/
theorem canonicalPositiveQHodgeSeedDerivative_eq_logarithmic_smul
    (q dq : ℝ) (hq : 0 < q) :
    canonicalPositiveQHodgeSeedDerivative q dq =
      (dq / (2 * q)) •
        canonicalHodgeStar (Real.sqrt (2 * q)) 0 := by
  have hamp := canonicalPositiveQAmplitudeDerivative_eq_logarithmic q dq hq
  unfold canonicalPositiveQHodgeSeedDerivative
  rw [hamp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHodgeStar, canonicalMaxwellTwoForm]

/-- Directional derivative of the transported Hodge seed. -/
noncomputable def transportedPositiveQHodgeSeedDerivative
    (L dL : Matrix4) (q dq : ℝ) : Matrix4 :=
  transportedTwoFormDerivative L dL
    (canonicalHodgeStar (Real.sqrt (2 * q)) 0)
    (canonicalPositiveQHodgeSeedDerivative q dq)

/-- The transported Hodge-seed derivative remains skew. -/
theorem transportedPositiveQHodgeSeedDerivative_transpose
    (L dL : Matrix4) (q dq : ℝ) :
    (transportedPositiveQHodgeSeedDerivative L dL q dq)ᵀ =
      -transportedPositiveQHodgeSeedDerivative L dL q dq := by
  apply transportedTwoFormDerivative_transpose
  · exact canonicalMaxwellTwoForm_transpose _ _
  · exact canonicalMaxwellTwoForm_transpose _ _

/-- Connection formula for the Hodge-seed derivative. -/
theorem transportedPositiveQHodgeSeedDerivative_eq_connectionFormula
    (L K dL : Matrix4) (q dq : ℝ) (hq : 0 < q)
    (hKL : K * L = 1) :
    transportedPositiveQHodgeSeedDerivative L dL q dq =
      transportTwoForm L
        ((lorentzFrameConnection dL K)ᵀ *
            canonicalHodgeStar (Real.sqrt (2 * q)) 0 +
          (dq / (2 * q)) •
            canonicalHodgeStar (Real.sqrt (2 * q)) 0 +
          canonicalHodgeStar (Real.sqrt (2 * q)) 0 *
            lorentzFrameConnection dL K) := by
  unfold transportedPositiveQHodgeSeedDerivative
  rw [transportedTwoFormDerivative_eq_connectionTransport L K dL _ _ hKL]
  rw [canonicalPositiveQHodgeSeedDerivative_eq_logarithmic_smul q dq hq]

/-- Four directional first derivatives of the transported positive-`q` seed. -/
noncomputable def localPositiveQSeedFirstDerivative
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4) : TwoFormFirstDerivative4 :=
  fun k => transportedPositiveQSeedDerivative L (dL k) q (dq k)

/-- Four directional first derivatives of its transported Hodge partner. -/
noncomputable def localPositiveQHodgeSeedFirstDerivative
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4) : TwoFormFirstDerivative4 :=
  fun k => transportedPositiveQHodgeSeedDerivative L (dL k) q (dq k)

/-- Exterior derivative of the reconstructed local seed. -/
noncomputable def localPositiveQSeedExteriorDerivative
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4) : ThreeTensor4 :=
  matrixExteriorDerivative (localPositiveQSeedFirstDerivative L dL q dq)

/-- Exterior derivative of the reconstructed local Hodge seed. -/
noncomputable def localPositiveQHodgeSeedExteriorDerivative
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4) : ThreeTensor4 :=
  matrixExteriorDerivative
    (localPositiveQHodgeSeedFirstDerivative L dL q dq)

/-- The reconstructed seed exterior derivative is an actual three-form. -/
theorem localPositiveQSeedExteriorDerivative_alternating
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4) :
    IsAlternatingThreeTensor
      (localPositiveQSeedExteriorDerivative L dL q dq) := by
  apply matrixExteriorDerivative_alternating
  intro k
  exact transportedPositiveQSeedDerivative_transpose L (dL k) q (dq k)

/-- The reconstructed Hodge-seed exterior derivative is an actual
three-form. -/
theorem localPositiveQHodgeSeedExteriorDerivative_alternating
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4) :
    IsAlternatingThreeTensor
      (localPositiveQHodgeSeedExteriorDerivative L dL q dq) := by
  apply matrixExteriorDerivative_alternating
  intro k
  exact transportedPositiveQHodgeSeedDerivative_transpose L (dL k) q (dq k)

/-- Exterior duality jet built entirely from a transported curvature seed and
its first chart jet. -/
noncomputable def localPositiveQExteriorDualityJet
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4)
    (c s : ℝ) (dc ds : OneForm4) :
    ExteriorDualityJet OneForm4 Matrix4 ThreeTensor4 where
  c := c
  s := s
  dc := dc
  ds := ds
  F0 := transportTwoForm L
    (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)
  G0 := transportedPositiveQHodgeSeed L q
  dF0 := localPositiveQSeedExteriorDerivative L dL q dq
  dG0 := localPositiveQHodgeSeedExteriorDerivative L dL q dq

/-- **Local curvature-seed EMD reduction.** The abstract exterior complexion
theorem now applies to the explicit transported seed.  Thus the full local
Bianchi/Maxwell equations are exactly the two computable seed-channel
three-form equations built from `L,dL,q,dq`. -/
theorem localPositiveQ_emdClosure_iff_seedChannels
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq omega v : OneForm4)
    (c s a : ℝ) (dc ds : OneForm4)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega) :
    let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
    EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo) ↔
      J.rotatedSeedDF =
          (a / 2) • matrixOneWedgeTwo v J.rotatedF -
            matrixOneWedgeTwo omega J.rotatedG ∧
        J.rotatedSeedDG =
          matrixOneWedgeTwo omega J.rotatedF -
            (a / 2) • matrixOneWedgeTwo v J.rotatedG := by
  dsimp only
  exact emdExteriorClosure_iff_seedChannels matrixOneWedgeTwo
    (localPositiveQExteriorDualityJet L dL q dq c s dc ds)
    omega v a hdc hds

/-- First local EMD obstruction three-form after the complexion product rule
has been removed. -/
noncomputable def localSeedEMDObstructionF
    (J : ExteriorDualityJet OneForm4 Matrix4 ThreeTensor4)
    (omega v : OneForm4) (a : ℝ) : ThreeTensor4 :=
  J.rotatedSeedDF -
    ((a / 2) • matrixOneWedgeTwo v J.rotatedF -
      matrixOneWedgeTwo omega J.rotatedG)

/-- Hodge-channel local EMD obstruction three-form. -/
noncomputable def localSeedEMDObstructionG
    (J : ExteriorDualityJet OneForm4 Matrix4 ThreeTensor4)
    (omega v : OneForm4) (a : ℝ) : ThreeTensor4 :=
  J.rotatedSeedDG -
    (matrixOneWedgeTwo omega J.rotatedF -
      (a / 2) • matrixOneWedgeTwo v J.rotatedG)

/-- **Necessary-and-sufficient local obstruction theorem.** For the explicit
curvature seed, EMD closure holds exactly when both computable three-form
obstructions vanish. -/
theorem localPositiveQ_emdClosure_iff_obstructions_zero
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq omega v : OneForm4)
    (c s a : ℝ) (dc ds : OneForm4)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega) :
    let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
    EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo) ↔
      localSeedEMDObstructionF J omega v a = 0 ∧
        localSeedEMDObstructionG J omega v a = 0 := by
  simpa only [localSeedEMDObstructionF, localSeedEMDObstructionG,
    sub_eq_zero] using
      (localPositiveQ_emdClosure_iff_seedChannels L dL q dq omega v
        c s a dc ds hdc hds)

/-- **Local generic orbit classification.** If the reconstructed seed solves
the EMD equations and the dilaton source is active, a constant duality rotate
of that same seed solves them only for the overall signs. -/
theorem localPositiveQ_constantDuality_eq_sign
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v : OneForm4)
    (c s a : ℝ) (hunit : c ^ 2 + s ^ 2 = 1) (ha : a ≠ 0)
    (hactive :
      matrixOneWedgeTwo v
          (transportTwoForm L
            (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)) ≠ 0 ∨
        matrixOneWedgeTwo v (transportedPositiveQHodgeSeed L q) ≠ 0)
    (hF0 : localPositiveQSeedExteriorDerivative L dL q dq =
      (a / 2) • matrixOneWedgeTwo v
        (transportTwoForm L
          (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)))
    (hG0 : localPositiveQHodgeSeedExteriorDerivative L dL q dq =
      -(a / 2) • matrixOneWedgeTwo v
        (transportedPositiveQHodgeSeed L q))
    (hFrot :
      c • localPositiveQSeedExteriorDerivative L dL q dq +
          s • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
        (a / 2) • matrixOneWedgeTwo v
          (c • transportTwoForm L
              (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
            s • transportedPositiveQHodgeSeed L q))
    (hGrot :
      (-s) • localPositiveQSeedExteriorDerivative L dL q dq +
          c • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
        -(a / 2) • matrixOneWedgeTwo v
          ((-s) • transportTwoForm L
              (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
            c • transportedPositiveQHodgeSeed L q)) :
    (c = 1 ∨ c = -1) ∧ s = 0 := by
  exact constantDuality_eq_sign_of_emd matrixOneWedgeTwo v
    (transportTwoForm L
      (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0))
    (transportedPositiveQHodgeSeed L q)
    (localPositiveQSeedExteriorDerivative L dL q dq)
    (localPositiveQHodgeSeedExteriorDerivative L dL q dq)
    c s a hunit ha hactive hF0 hG0 hFrot hGrot

end RainichKaluza
