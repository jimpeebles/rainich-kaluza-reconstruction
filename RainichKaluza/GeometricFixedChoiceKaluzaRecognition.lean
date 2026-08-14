import RainichKaluza.FixedChoiceKaluzaRecognition
import RainichKaluza.NormalGaugeEquationBridge

/-!
# Geometric fixed-choice recognition input

`FixedChoiceKaluzaRecognition` isolates the actual `C²` representative used
by the Kaluza backend.  This file removes its weighted-Maxwell equation as a
primitive hypothesis on a Minkowski normal-coordinate germ.  The replacement
is the ordinary geometric divergence equation for the curvature of the
representative gauge potential; `NormalGaugeEquationBridge` proves that this
is exactly the mixed Kaluza Ricci block.
-/

namespace RainichKaluza

open Set Filter
open scoped Topology

/-- One compatible `C²` representative at a Minkowski normal point, with the
weighted Maxwell input stated as a divergence law for its physical curvature
rather than as a Kaluza Ricci residual. -/
structure FixedChoiceMinkowskiNormalGaugeRepresentativeAt
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    B.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  scalar_germ : product.fields.phi =ᶠ[𝓝 x]
    B.physical.maxwell.scalarRepresentative
  potential_germ : product.fields.potential =ᶠ[𝓝 x]
    fun y i => gaugePotential y (coordinateDirection i)
  metric_germ : product.fields.metric =ᶠ[𝓝 x]
    coordinateMetricMatrixField4 g
  diagonal_eq_minkowski : product.fields.diagonal = minkowskiSign
  einstein : NormalGaugeEinsteinEquations product
  weightedMaxwellDivergence : NormalWeightedMaxwellDivergence
    (gaugeCurvatureOfFirstJet product.fields.A1)
    (gaugeCurvatureFirstJetOfSecondJet product.fields.A2)
    product.fields.phi1 (Real.sqrt 3)
  scalarResidual : normalGaugeScalarEquationResidual product =
    actualMetricScalarEquationResidualCandidateAt4 g choice x

namespace FixedChoiceMinkowskiNormalGaugeRepresentativeAt

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
  {B : FixedChoiceStagedKaluzaConverseBoundary D C M branch}
  {x : CurvatureCoordinateSpace4}

/-- Forget the geometric presentation after deriving the backend's complete
weighted-Maxwell block. -/
def toNormalGaugeRepresentative
    (N : FixedChoiceMinkowskiNormalGaugeRepresentativeAt B x) :
    FixedChoiceNormalGaugeRepresentativeAt B x where
  point_mem := N.point_mem
  gaugePotential := N.gaugePotential
  gaugePotential_is := N.gaugePotential_is
  product := N.product
  scalar_germ := N.scalar_germ
  potential_germ := N.potential_germ
  metric_germ := N.metric_germ
  einstein := N.einstein
  weightedMaxwell := by
    intro n
    rw [N.diagonal_eq_minkowski]
    exact conventionWeightedMaxwellResidual_minkowski_eq_zero_of_divergence
      N.product.fields.phi1 N.product.fields.A1 N.product.fields.A2
        N.weightedMaxwellDivergence n
  scalarResidual := N.scalarResidual

/-- The normal-gauge EMD equations follow from the staged scalar residual,
the Einstein block, and the physical weighted-divergence equation. -/
theorem realized_emd
    (N : FixedChoiceMinkowskiNormalGaugeRepresentativeAt B x) :
    N.product.fields.EMDEquations :=
  B.realized_emd N.toNormalGaugeRepresentative

end FixedChoiceMinkowskiNormalGaugeRepresentativeAt

/-! ## Exterior-Hodge formulation -/

/-- A Minkowski normal-gauge representative whose Maxwell input is stated
entirely as the exterior equation

`d(*F) = -sqrt(3) dphi wedge (*F)`.

Here `F` and its first jet are extracted literally from the first and second
jets of the representative potential.  Thus neither a divergence equation
nor a mixed Kaluza Ricci component is assumed. -/
structure FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    B.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  scalar_germ : product.fields.phi =ᶠ[𝓝 x]
    B.physical.maxwell.scalarRepresentative
  potential_germ : product.fields.potential =ᶠ[𝓝 x]
    fun y i => gaugePotential y (coordinateDirection i)
  metric_germ : product.fields.metric =ᶠ[𝓝 x]
    coordinateMetricMatrixField4 g
  diagonal_eq_minkowski : product.fields.diagonal = minkowskiSign
  einstein : NormalGaugeEinsteinEquations product
  hodgeExterior :
    matrixExteriorDerivative
        (fun k => coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureFirstJetOfSecondJet product.fields.A2 k)) =
      -(Real.sqrt 3) • matrixOneWedgeTwoTensor product.fields.phi1
        (coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureOfFirstJet product.fields.A1))
  scalarResidual : normalGaugeScalarEquationResidual product =
    actualMetricScalarEquationResidualCandidateAt4 g choice x

namespace FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
  {B : FixedChoiceStagedKaluzaConverseBoundary D C M branch}
  {x : CurvatureCoordinateSpace4}

/-- Convert the exterior-Hodge equation to the physical weighted-divergence
input used by the preceding recognition theorem. -/
def toDivergenceRepresentative
    (N : FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt B x) :
    FixedChoiceMinkowskiNormalGaugeRepresentativeAt B x where
  point_mem := N.point_mem
  gaugePotential := N.gaugePotential
  gaugePotential_is := N.gaugePotential_is
  product := N.product
  scalar_germ := N.scalar_germ
  potential_germ := N.potential_germ
  metric_germ := N.metric_germ
  diagonal_eq_minkowski := N.diagonal_eq_minkowski
  einstein := N.einstein
  weightedMaxwellDivergence := by
    exact normalWeightedMaxwellDivergence_of_minkowskiHodgeExterior
      (gaugeCurvatureOfFirstJet N.product.fields.A1)
      (coordinateMetricHodgeTwoForm4 minkowskiMetric
        (gaugeCurvatureOfFirstJet N.product.fields.A1))
      (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2)
      (fun k => coordinateMetricHodgeTwoForm4 minkowskiMetric
        (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k))
      N.product.fields.phi1 (Real.sqrt 3)
      (gaugeCurvatureOfFirstJet_transpose N.product.fields.A1)
      (gaugeCurvatureFirstJetOfSecondJet_transpose N.product.fields.A2)
      rfl (fun _ => rfl) N.hodgeExterior
  scalarResidual := N.scalarResidual

/-- The staged data and the exterior-Hodge equation imply the complete
normal-gauge EMD system. -/
theorem realized_emd
    (N : FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt B x) :
    N.product.fields.EMDEquations :=
  N.toDivergenceRepresentative.realized_emd

end FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt

namespace FixedChoiceStagedKaluzaConverseBoundary

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
  {x : CurvatureCoordinateSpace4}

/-- Fixed-choice recognition with the Maxwell equation supplied in its
geometric divergence form. -/
theorem exists_completeFixedChoiceKaluzaRecognition_of_weightedDivergence
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (N : FixedChoiceMinkowskiNormalGaugeRepresentativeAt B x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition B
      N.toNormalGaugeRepresentative) :=
  B.exists_completeFixedChoiceKaluzaRecognition
    N.toNormalGaugeRepresentative

/-- Fixed-choice recognition with the Maxwell equation supplied directly by
the physical exterior-Hodge channel. -/
theorem exists_completeFixedChoiceKaluzaRecognition_of_hodgeExterior
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (N : FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt B x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition B
      N.toDivergenceRepresentative.toNormalGaugeRepresentative) :=
  B.exists_completeFixedChoiceKaluzaRecognition_of_weightedDivergence
    N.toDivergenceRepresentative

end FixedChoiceStagedKaluzaConverseBoundary

end RainichKaluza
