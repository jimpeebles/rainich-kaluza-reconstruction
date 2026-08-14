import RainichKaluza.NormalMaxwellHodgeBridge
import RainichKaluza.KaluzaRicciBase
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Normal-gauge EMD equation bridges

This file identifies the mixed Kaluza Ricci residual with the ordinary
weighted Maxwell divergence in the Minkowski normal frame.  It is deliberately
an algebraic jet statement: the first and second jets of a gauge potential are
converted to the value and first jet of its curvature, and every sign and
factor is then checked componentwise.
-/

namespace RainichKaluza

open scoped Matrix

/-- Curvature of the first coordinate jet of a gauge potential. -/
def gaugeCurvatureOfFirstJet
    (A1 : Fin 4 → Fin 4 → ℝ) : Matrix4 :=
  fun i j => A1 i j - A1 j i

/-- Directional first jet of the gauge curvature, extracted from the second
coordinate jet of its potential. -/
def gaugeCurvatureFirstJetOfSecondJet
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ) : Fin 4 → Matrix4 :=
  fun k i j => A2 k i j - A2 k j i

/-- Curvature extracted from any potential first jet is alternating. -/
theorem gaugeCurvatureOfFirstJet_transpose
    (A1 : Fin 4 → Fin 4 → ℝ) :
    (gaugeCurvatureOfFirstJet A1)ᵀ =
      -gaugeCurvatureOfFirstJet A1 := by
  ext i j
  simp [gaugeCurvatureOfFirstJet]

/-- Every directional derivative extracted from a potential second jet is
alternating in the curvature slots. -/
theorem gaugeCurvatureFirstJetOfSecondJet_transpose
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ) (k : Fin 4) :
    (gaugeCurvatureFirstJetOfSecondJet A2 k)ᵀ =
      -gaugeCurvatureFirstJetOfSecondJet A2 k := by
  ext i j
  simp [gaugeCurvatureFirstJetOfSecondJet]

/-- Normal-coordinate form of `∇_μ F^{μr} = -a v_μ F^{μr}` for the
physical, convention-normalized Maxwell field. -/
def NormalWeightedMaxwellDivergence
    (F : Matrix4) (DF : Fin 4 → Matrix4) (v : OneForm4) (a : ℝ) : Prop :=
  ∀ r,
    normalTwoFormDivergence DF r =
      -a * ∑ i, v i * normalRaisedTwoForm F i r

/-- The rescaled Hodge/exterior bridge specializes directly to the physical
weighted Maxwell equation after replacing its parameter by `2a`. -/
theorem normalWeightedMaxwellDivergence_of_minkowskiHodgeExterior
    (F G : Matrix4) (DF DG : Fin 4 → Matrix4)
    (v : OneForm4) (a : ℝ)
    (hF : Fᵀ = -F) (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hG : G = coordinateMetricHodgeTwoForm4 minkowskiMetric F)
    (hDG : ∀ k,
      DG k = coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k))
    (hExterior :
      matrixExteriorDerivative DG =
        -a • matrixOneWedgeTwoTensor v G) :
    NormalWeightedMaxwellDivergence F DF v a := by
  have h := normalRescaledMaxwellDivergence_of_minkowskiHodgeExterior
    F G DF DG v (2 * a) hF hDF hG hDG
  have hscale : -(2 * a / 2) = -a := by ring
  have hres : NormalRescaledMaxwellDivergence F DF v (2 * a) := by
    apply h
    simpa [hscale] using hExterior
  intro r
  simpa [NormalRescaledMaxwellDivergence, hscale] using hres r

/-- Exact component identity relating the backend's mixed Kaluza residual to
the physical weighted Maxwell divergence. -/
theorem conventionWeightedMaxwellResidual_minkowski_eq
    (v : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ) (n : Fin 4) :
    conventionWeightedMaxwellResidual minkowskiSign v A1 A2 n =
      -minkowskiSign n *
        (normalTwoFormDivergence
            (gaugeCurvatureFirstJetOfSecondJet A2) n +
          Real.sqrt 3 * ∑ i,
            v i * normalRaisedTwoForm
              (gaugeCurvatureOfFirstJet A1) i n) := by
  fin_cases n <;>
    simp [conventionWeightedMaxwellResidual,
      gaugeCurvatureOfFirstJet, gaugeCurvatureFirstJetOfSecondJet,
      normalTwoFormDivergence, normalRaisedTwoForm, minkowskiSign,
      Fin.sum_univ_succ] <;>
    ring

/-- The physical weighted Maxwell divergence discharges the complete mixed
normal-frame equation block of the Kaluza backend. -/
theorem conventionWeightedMaxwellResidual_minkowski_eq_zero_of_divergence
    (v : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hMaxwell : NormalWeightedMaxwellDivergence
      (gaugeCurvatureOfFirstJet A1)
      (gaugeCurvatureFirstJetOfSecondJet A2) v (Real.sqrt 3)) :
    ∀ n,
      conventionWeightedMaxwellResidual minkowskiSign v A1 A2 n = 0 := by
  intro n
  rw [conventionWeightedMaxwellResidual_minkowski_eq]
  rw [hMaxwell n]
  ring

end RainichKaluza
