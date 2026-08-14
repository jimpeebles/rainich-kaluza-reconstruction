import RainichKaluza.CoreEinsteinSourceBridge

/-!
# Normal scalar derivation with the Einstein source supplied by the core

`FixedChoiceNormalEMDScalarDerivationAt` originally exposed neighborhood
Einstein/source equality as a field.  The scalar-residual-free staged core now
proves that equality from its Ricci entrance and normalized Maxwell stress.
This module removes that redundant field and reconstructs the original
package from seed alignment.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

/-- All analytic and matter-jet inputs of the normal scalar derivation except
the Einstein/source identity, which is derived from the staged core below. -/
structure FixedChoiceNormalMatterJetDerivationAt
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4) where
  metricC3 : CoordinateMetricComponentsContDiffThreeAt4 g z
  metricSymmetricNear : CoordinateMetricSymmetricNear4 g z
  metricDifferentiable :
    MatrixFieldDifferentiableAt4 (coordinateMetricMatrixField4 g) z
  metricValue : coordinateMetricMatrixField4 g z = minkowskiMetric
  metricFirstJet : actualCoordinateMetricJet1Field4 g z = 0
  scalarJet : Fin 4 → OneForm4
  maxwellJet : Fin 4 → Matrix4
  hodgeJet : Fin 4 → Matrix4
  hodgeValue : Matrix4
  scalarComponentsDifferentiable : ∀ k,
    DifferentiableAt ℝ
      (fun y ↦ actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y k) z
  scalarFirstJet : ∀ r k,
    scalarFieldCoordinateFDeriv
      (fun y ↦ actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y k) z r = scalarJet r k
  maxwellComponentsDifferentiable : ∀ p q,
    DifferentiableAt ℝ
      (fun y ↦ K.curvatureNormalizedPhysicalMaxwellMatrix4 y p q) z
  maxwellFirstJet : ∀ r p q,
    scalarFieldCoordinateFDeriv
      (fun y ↦ K.curvatureNormalizedPhysicalMaxwellMatrix4 y p q) z r =
        maxwellJet r p q
  scalarJet_symmetric : ∀ i j, scalarJet i j = scalarJet j i
  maxwellValue_skew :
    (K.curvatureNormalizedPhysicalMaxwellMatrix4 z)ᵀ =
      -K.curvatureNormalizedPhysicalMaxwellMatrix4 z
  maxwellJet_skew : ∀ k, (maxwellJet k)ᵀ = -maxwellJet k
  maxwellBianchi : NormalRescaledMaxwellBianchi
    (K.curvatureNormalizedPhysicalMaxwellMatrix4 z) maxwellJet
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z) M.coupling
  hodgeValue_eq : hodgeValue = coordinateMetricHodgeTwoForm4
    minkowskiMetric (K.curvatureNormalizedPhysicalMaxwellMatrix4 z)
  hodgeJet_eq : ∀ k, hodgeJet k = coordinateMetricHodgeTwoForm4
    minkowskiMetric (maxwellJet k)
  hodgeExterior : matrixExteriorDerivative hodgeJet =
    -(M.coupling / 2) • matrixOneWedgeTwoTensor
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus z) hodgeValue
  scalarCovector_active : actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus z ≠ 0
  metricResidual_eq_normal :
    actualMetricScalarEquationResidualCandidateAt4 g choice z =
      normalScalarEquationResidual scalarJet
        (K.curvatureNormalizedPhysicalMaxwellMatrix4 z) M.coupling

namespace FixedChoiceNormalMatterJetDerivationAt

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
  {K : FixedChoiceStagedKaluzaConverseCore D C M branch}
  {z : CurvatureCoordinateSpace4}

/-- Seed alignment supplies the omitted neighborhood Einstein/source field,
turning the reduced analytic package into the established normal scalar
derivation. -/
def withCoreEinsteinSource
    (H : FixedChoiceNormalMatterJetDerivationAt K z)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (hz : z ∈ U) :
    FixedChoiceNormalEMDScalarDerivationAt K z where
  metricC3 := H.metricC3
  metricSymmetricNear := H.metricSymmetricNear
  metricDifferentiable := H.metricDifferentiable
  metricValue := H.metricValue
  metricFirstJet := H.metricFirstJet
  scalarJet := H.scalarJet
  maxwellJet := H.maxwellJet
  hodgeJet := H.hodgeJet
  hodgeValue := H.hodgeValue
  scalarComponentsDifferentiable := H.scalarComponentsDifferentiable
  scalarFirstJet := H.scalarFirstJet
  maxwellComponentsDifferentiable := H.maxwellComponentsDifferentiable
  maxwellFirstJet := H.maxwellFirstJet
  scalarJet_symmetric := H.scalarJet_symmetric
  maxwellValue_skew := H.maxwellValue_skew
  maxwellJet_skew := H.maxwellJet_skew
  maxwellBianchi := H.maxwellBianchi
  hodgeValue_eq := H.hodgeValue_eq
  hodgeJet_eq := H.hodgeJet_eq
  hodgeExterior := H.hodgeExterior
  scalarCovector_active := H.scalarCovector_active
  einsteinSourceNear :=
    K.actualCoordinateEinsteinField4_eventuallyEq_actualMatterSource
      halign z hz
  metricResidual_eq_normal := H.metricResidual_eq_normal

end FixedChoiceNormalMatterJetDerivationAt

end RainichKaluza
