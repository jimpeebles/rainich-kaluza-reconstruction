import RainichKaluza.MatterStressDivergence
import RainichKaluza.ThirdOrderMatterJetAmbiguity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Normal-coordinate Hodge/exterior to Maxwell-divergence bridge

At a Minkowski normal-coordinate point the metric first jet vanishes, so the
first jet of `G = *F` is obtained by applying the fixed Minkowski Hodge map to
each directional first derivative of `F`.  This file proves, by an explicit
four-dimensional component calculation, that the exterior equation

`dG = -(a/2) v ∧ G`

is exactly the weighted coordinate-divergence equation for `F` used by the
normal-coordinate matter Noether identity.

The hypotheses explicitly retain all of the data that would have to be
supplied by a field-level argument: skewness of the value and every first-jet
matrix, Hodge compatibility of the value, and Hodge compatibility of the
first jet.  No arbitrary-chart covariance or differentiation of a varying
metric Hodge operator is claimed here.
-/

namespace RainichKaluza

open scoped Matrix

/-- **Minkowski Hodge/exterior to weighted Maxwell divergence.**  If `G` and
its first jet are the Minkowski Hodge duals of `F` and its first jet, then the
rescaled Hodge-channel exterior equation implies

`partial_mu F^{mu r} = -(a/2) v_mu F^{mu r}`.

The sign is the one induced by the repository conventions
`epsilon(0,1,2,3)=+1`, signature `(-,+,+,+)`, and
`*(e⁰∧e¹)=e²∧e³`. -/
theorem normalRescaledMaxwellDivergence_of_minkowskiHodgeExterior
    (F G : Matrix4) (DF DG : Fin 4 → Matrix4)
    (v : OneForm4) (a : ℝ)
    (hF : Fᵀ = -F) (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hG : G = coordinateMetricHodgeTwoForm4 minkowskiMetric F)
    (hDG : ∀ k,
      DG k = coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k))
    (hExterior :
      matrixExteriorDerivative DG =
        -(a / 2) • matrixOneWedgeTwoTensor v G) :
    NormalRescaledMaxwellDivergence F DF v a := by
  have hFnorm := eq_lorentzSkewTwoForm4_of_transpose_eq_neg F hF
  have hD0 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (DF 0) (hDF 0)
  have hD1 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (DF 1) (hDF 1)
  have hD2 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (DF 2) (hDF 2)
  have hD3 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (DF 3) (hDF 3)
  have hDnorm : DF = fun k => lorentzSkewTwoForm4
      (DF k 0 1) (DF k 0 2) (DF k 0 3)
      (DF k 2 3) (DF k 3 1) (DF k 1 2) := by
    funext k
    exact eq_lorentzSkewTwoForm4_of_transpose_eq_neg (DF k) (hDF k)
  unfold NormalRescaledMaxwellDivergence
  rw [hDnorm, hFnorm]
  intro r
  fin_cases r
  · have h := congrFun (congrFun (congrFun hExterior 1) 2) 3
    simp only [matrixExteriorDerivative, Pi.smul_apply,
      smul_eq_mul, neg_mul, matrixOneWedgeTwoTensor] at h
    rw [hDG 1, hDG 2, hDG 3, hG, hFnorm, hD1, hD2, hD3,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew] at h
    simp [normalTwoFormDivergence, normalRaisedTwoForm,
      lorentzSkewTwoForm4, minkowskiSign,
      Fin.sum_univ_succ] at h ⊢
    linarith
  · have h := congrFun (congrFun (congrFun hExterior 0) 2) 3
    simp only [matrixExteriorDerivative, Pi.smul_apply,
      smul_eq_mul, neg_mul, matrixOneWedgeTwoTensor] at h
    rw [hDG 0, hDG 2, hDG 3, hG, hFnorm, hD0, hD2, hD3,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew] at h
    simp [normalTwoFormDivergence, normalRaisedTwoForm,
      lorentzSkewTwoForm4, minkowskiSign,
      Fin.sum_univ_succ] at h ⊢
    linarith
  · have h := congrFun (congrFun (congrFun hExterior 0) 3) 1
    simp only [matrixExteriorDerivative, Pi.smul_apply,
      smul_eq_mul, neg_mul, matrixOneWedgeTwoTensor] at h
    rw [hDG 0, hDG 3, hDG 1, hG, hFnorm, hD0, hD3, hD1,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew] at h
    simp [normalTwoFormDivergence, normalRaisedTwoForm,
      lorentzSkewTwoForm4, minkowskiSign,
      Fin.sum_univ_succ] at h ⊢
    linarith
  · have h := congrFun (congrFun (congrFun hExterior 0) 1) 2
    simp only [matrixExteriorDerivative, Pi.smul_apply,
      smul_eq_mul, neg_mul, matrixOneWedgeTwoTensor] at h
    rw [hDG 0, hDG 1, hDG 2, hG, hFnorm, hD0, hD1, hD2,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew,
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew] at h
    simp [normalTwoFormDivergence, normalRaisedTwoForm,
      lorentzSkewTwoForm4, minkowskiSign,
      Fin.sum_univ_succ] at h ⊢
    linarith

/-- The normal-coordinate matter Noether identity with the Maxwell equation
supplied directly in its geometric exterior-Hodge form.  The conclusion uses
the raw first variation of the Maxwell stress, so neither the Hodge-to-
divergence conversion nor the finite alternating-contraction algebra remains
as a hypothesis. -/
theorem normalRawMatterStressDivergence_eq_scalarResidual_of_minkowskiHodgeExterior
    (v : OneForm4) (Dv : Fin 4 → OneForm4)
    (F G : Matrix4) (DF DG : Fin 4 → Matrix4) (a : ℝ)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : Fᵀ = -F) (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hBianchi : NormalRescaledMaxwellBianchi F DF v a)
    (hG : G = coordinateMetricHodgeTwoForm4 minkowskiMetric F)
    (hDG : ∀ k,
      DG k = coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k))
    (hExterior :
      matrixExteriorDerivative DG =
        -(a / 2) • matrixOneWedgeTwoTensor v G) :
    normalScalarEinsteinStressDivergence v Dv +
      normalMaxwellStressFirstJetDivergence F DF =
        (1 / 2 * normalScalarEquationResidual Dv F a) • v := by
  have hMaxwell : NormalRescaledMaxwellDivergence F DF v a :=
    normalRescaledMaxwellDivergence_of_minkowskiHodgeExterior
      F G DF DG v a hF hDF hG hDG hExterior
  rw [normalMaxwellStressFirstJetDivergence_eq F DF hF hDF]
  exact normalMatterStressDivergence_eq_scalarResidual
    v Dv F DF a hDv hF hBianchi hMaxwell

/-- On the active scalar branch, vanishing of the raw differentiated matter
source now forces the scalar residual using only the Bianchi equation and the
exterior equation for the actual Hodge partner. -/
theorem normalScalarEquationResidual_eq_zero_of_rawMatterDivergence_hodgeExterior
    (v : OneForm4) (Dv : Fin 4 → OneForm4)
    (F G : Matrix4) (DF DG : Fin 4 → Matrix4) (a : ℝ)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : Fᵀ = -F) (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hBianchi : NormalRescaledMaxwellBianchi F DF v a)
    (hG : G = coordinateMetricHodgeTwoForm4 minkowskiMetric F)
    (hDG : ∀ k,
      DG k = coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k))
    (hExterior :
      matrixExteriorDerivative DG =
        -(a / 2) • matrixOneWedgeTwoTensor v G)
    (hv : v ≠ 0)
    (hdiv : normalScalarEinsteinStressDivergence v Dv +
      normalMaxwellStressFirstJetDivergence F DF = 0) :
    normalScalarEquationResidual Dv F a = 0 := by
  have hMaxwell : NormalRescaledMaxwellDivergence F DF v a :=
    normalRescaledMaxwellDivergence_of_minkowskiHodgeExterior
      F G DF DG v a hF hDF hG hDG hExterior
  rw [normalMaxwellStressFirstJetDivergence_eq F DF hF hDF] at hdiv
  exact normalScalarEquationResidual_eq_zero_of_matterDivergence
    v Dv F DF a hDv hF hBianchi hMaxwell hv hdiv

end RainichKaluza
