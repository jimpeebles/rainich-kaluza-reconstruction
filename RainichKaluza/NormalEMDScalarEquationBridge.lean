import RainichKaluza.CoordinateEinsteinRegularity
import RainichKaluza.EinsteinSourceFirstJetBridge
import RainichKaluza.NormalMaxwellHodgeBridge

/-!
# Normal-point Einstein-to-scalar-equation assembly

This file composes the two normal-coordinate halves of the Kaluza converse
Noether argument.  The actual `C³` coordinate Einstein tensor has zero
contracted divergence, while the scalar and Maxwell first jets have divergence
equal to one half of the scalar equation residual times the active scalar
covector.

The first theorem states the source-divergence seam explicitly.  The second
closes it from an actual neighborhood Einstein/source equality, using the
moving-metric first-jet reduction in `EinsteinSourceFirstJetBridge`.  What
remains upstream is constructing that neighborhood equality and its field
jets from the full converse hypotheses; arbitrary-coordinate covariance is
also not claimed here.
-/

namespace RainichKaluza

open scoped Matrix

/-- **Normal-point scalar equation from actual contracted Bianchi.**  At a
Minkowski normal-coordinate point of a symmetric `C³` metric, the actual
contracted Bianchi theorem and the exterior-form Maxwell equations force the
scalar residual to vanish on the active branch, once the differentiated
Einstein/source identification is supplied. -/
theorem normalScalarEquationResidual_eq_zero_of_actualEinsteinBianchi
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hC3 : CoordinateMetricComponentsContDiffThreeAt4 g z)
    (hsymm : CoordinateMetricSymmetricNear4 g z)
    (hmetric : coordinateMetricMatrixField4 g z = minkowskiMetric)
    (hfirst : actualCoordinateMetricJet1Field4 g z = 0)
    (v : OneForm4) (Dv : Fin 4 → OneForm4)
    (F G : Matrix4) (DF DG : Fin 4 → Matrix4) (a : ℝ)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : Fᵀ = -F) (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hMaxwellBianchi : NormalRescaledMaxwellBianchi F DF v a)
    (hG : G = coordinateMetricHodgeTwoForm4 minkowskiMetric F)
    (hDG : ∀ k,
      DG k = coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k))
    (hHodgeExterior :
      matrixExteriorDerivative DG =
        -(a / 2) • matrixOneWedgeTwoTensor v G)
    (hv : v ≠ 0)
    (hEinsteinSource : ∀ j,
      actualCoordinateEinsteinContractedDivergenceAt4 g z j =
        (normalScalarEinsteinStressDivergence v Dv +
          normalMaxwellStressFirstJetDivergence F DF) j) :
    normalScalarEquationResidual Dv F a = 0 := by
  have hEinsteinZero : ∀ j,
      actualCoordinateEinsteinContractedDivergenceAt4 g z j = 0 :=
    actualCoordinateEinsteinField4_contractedBianchi_of_minkowskiNormal_C3
      g z hC3 hsymm hmetric hfirst
  have hMatterZero : normalScalarEinsteinStressDivergence v Dv +
      normalMaxwellStressFirstJetDivergence F DF = 0 := by
    funext j
    rw [← hEinsteinSource j]
    exact hEinsteinZero j
  exact
    normalScalarEquationResidual_eq_zero_of_rawMatterDivergence_hodgeExterior
      v Dv F G DF DG a hDv hF hDF hMaxwellBianchi hG hDG
      hHodgeExterior hv hMatterZero

/-- **Normal-point scalar equation from a neighborhood Einstein equation.**
This closes the source-differentiation seam in the preceding theorem.  An
actual neighborhood equality between the coordinate Einstein tensor and the
honest metric-dependent scalar-plus-Maxwell source differentiates to the raw
normal matter-stress divergence; contracted Bianchi and the two exterior
Maxwell equations then force the scalar residual on the active branch. -/
theorem normalScalarEquationResidual_eq_zero_of_eventuallyEqEinsteinSource
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hC3 : CoordinateMetricComponentsContDiffThreeAt4 g z)
    (hsymm : CoordinateMetricSymmetricNear4 g z)
    (hg : MatrixFieldDifferentiableAt4 (coordinateMetricMatrixField4 g) z)
    (hmetric : coordinateMetricMatrixField4 g z = minkowskiMetric)
    (hfirst : actualCoordinateMetricJet1Field4 g z = 0)
    (Dv : Fin 4 → OneForm4) (DF DG : Fin 4 → Matrix4)
    (G : Matrix4) (a : ℝ)
    (hvDiff : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ r k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k)
    (hFDiff : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ r p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : (FField z)ᵀ = -FField z)
    (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hMaxwellBianchi :
      NormalRescaledMaxwellBianchi (FField z) DF (vField z) a)
    (hG : G = coordinateMetricHodgeTwoForm4 minkowskiMetric (FField z))
    (hDG : ∀ k,
      DG k = coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k))
    (hHodgeExterior :
      matrixExteriorDerivative DG =
        -(a / 2) • matrixOneWedgeTwoTensor (vField z) G)
    (hv : vField z ≠ 0)
    (hEinsteinSource :
      actualCoordinateEinsteinField4 g =ᶠ[nhds z]
        actualCoordinateMatterEinsteinStressCovariantField4
          g vField FField) :
    normalScalarEquationResidual Dv (FField z) a = 0 := by
  apply normalScalarEquationResidual_eq_zero_of_actualEinsteinBianchi
    g z hC3 hsymm hmetric hfirst (vField z) Dv (FField z) G DF DG a
    hDv hF hDF hMaxwellBianchi hG hDG hHodgeExterior hv
  intro j
  exact
    actualCoordinateEinsteinContractedDivergenceAt4_eq_normalMatterStressDivergence_of_eventuallyEq
      g vField FField z Dv DF hg hmetric hfirst hvDiff hvJet
      hFDiff hFJet hEinsteinSource j

end RainichKaluza
