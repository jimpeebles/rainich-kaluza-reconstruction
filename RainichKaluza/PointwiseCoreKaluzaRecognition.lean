import RainichKaluza.ScalarResidualFreeStagedKaluzaConverse

/-!
# Pointwise recognition from the scalar-residual-free staged core

The scalar equation is a pointwise consequence of the normal-coordinate
Noether/Bianchi argument.  Requiring such a normal chart simultaneously at
every point of a fixed coordinate patch is artificial.  This file therefore
performs recognition at one selected point directly from
`FixedChoiceStagedKaluzaConverseCore`.

The patch-level core still supplies the genuine scalar and Maxwell fields,
their potentials and orbit statements, and the algebraic metric entrance.
Only the normal representative and the scalar derivation are pointwise.  The
normal Einstein and geometric weighted-Maxwell equations remain explicit
fields of the representative; the scalar block is derived from
`FixedChoiceNormalEMDScalarDerivationAt.metricResidual_zero`.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

/-- A compatible `C²` normal/radial-gauge representative for a pre-scalar
staged core at one point.  The weighted Maxwell input is geometric divergence
rather than a backend Kaluza residual.  No scalar equation is stored. -/
structure FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt
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
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    K.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  scalar_germ : product.fields.phi =ᶠ[nhds x]
    K.physical.maxwell.scalarRepresentative
  potential_germ : product.fields.potential =ᶠ[nhds x]
    fun y i ↦ gaugePotential y (coordinateDirection i)
  metric_germ : product.fields.metric =ᶠ[nhds x]
    coordinateMetricMatrixField4 g
  diagonal_eq_minkowski : product.fields.diagonal = minkowskiSign
  einstein : NormalGaugeEinsteinEquations product
  weightedMaxwellDivergence : NormalWeightedMaxwellDivergence
    (gaugeCurvatureOfFirstJet product.fields.A1)
    (gaugeCurvatureFirstJetOfSecondJet product.fields.A2)
    product.fields.phi1 (Real.sqrt 3)
  scalarResidual : normalGaugeScalarEquationResidual product =
    actualMetricScalarEquationResidualCandidateAt4 g choice x

namespace FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt

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
  {x : CurvatureCoordinateSpace4}

/-- The geometric weighted-divergence equation gives the backend Maxwell
block exactly as in `GeometricFixedChoiceKaluzaRecognition`. -/
theorem weightedMaxwell
    (N : FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt K x) :
    NormalGaugeWeightedMaxwellEquations N.product := by
  intro n
  rw [N.diagonal_eq_minkowski]
  exact conventionWeightedMaxwellResidual_minkowski_eq_zero_of_divergence
    N.product.fields.phi1 N.product.fields.A1 N.product.fields.A2
      N.weightedMaxwellDivergence n

/-- **Pointwise EMD closure.**  Einstein and weighted Maxwell remain honest
representative inputs.  The scalar block is not assumed: its normal residual
is derived from `H`, identified with the representative residual, and then
inserted directly at the selected point. -/
theorem realized_emd_of_normalScalarDerivation
    (N : FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt K x)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x) :
    N.product.fields.EMDEquations := by
  rw [lorentzianKaluza_emDEquations_iff]
  refine ⟨N.einstein, N.weightedMaxwell, ?_⟩
  rw [N.scalarResidual]
  exact H.metricResidual_zero K x

end FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt

/-- Complete pointwise local recognition output from the pre-scalar staged
core.  It is the same Ricci-flat, converse-reduction, and orbit conclusion as
`CompleteFixedChoiceKaluzaRecognition`, but it does not manufacture a
patchwide scalar-residual proof merely to state a result at `x`. -/
structure CompletePointwiseCoreKaluzaRecognition
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    {x : CurvatureCoordinateSpace4}
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (N : FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt K x) where
  scalarPotential : CurvatureCoordinateSpace4 → ℝ
  scalarPotential_eq : scalarPotential =
    K.physical.maxwell.scalarRepresentative
  scalarPotential_is : IsScalarPotentialOn scalarPotential
    (C.branchScalarOneForm branch) U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_eq : gaugePotential = N.gaugePotential
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    K.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  product_eq : product = N.product
  product_scalar_germ : product.fields.phi =ᶠ[nhds x] scalarPotential
  product_potential_germ : product.fields.potential =ᶠ[nhds x]
    fun y i ↦ gaugePotential y (coordinateDirection i)
  baseMetric_germ : product.fields.metric =ᶠ[nhds x]
    coordinateMetricMatrixField4 g
  emd_equations : product.fields.EMDEquations
  intrinsic_ricciFlat : ∀ z : ℝ, product.IntrinsicRicciFlatAt z
  nonlinear_coordinate_ricciFlat :
    ∀ (T : CoordinateChangeJet3 (Fin 4 ⊕ Unit)) (z : ℝ),
      product.fields.NonlinearLocalProductCoordinateRicciFlat T z
  converse_reduction : ∀ z : ℝ,
    product.IntrinsicRicciFlatAt z ↔ product.fields.EMDEquations
  scalar_orbit :
    ∀ psi : CurvatureCoordinateSpace4 → ℝ,
      IsScalarPotentialOn psi (C.branchScalarOneForm branch) U →
      ∃ c : ℝ, U.EqOn scalarPotential (fun y ↦ psi y + c)
  gauge_orbit :
    ∀ A' : CurvatureCoordinateSpace4 →
        CurvatureCoordinateSpace4 →L[ℝ] ℝ,
      IsGaugePotentialOn A'
        K.physical.maxwell.conventionNormalizedPhysicalMaxwell U →
      ∃ chi : CurvatureCoordinateSpace4 → ℝ,
        IsScalarPotentialOn chi (A' - gaugePotential) U
  positive_coupling_orientation :
    M.coupling = Real.sqrt 3 ∨ -M.coupling = Real.sqrt 3
  presentation_orbit_complete :
    ∀ (P Q : KaluzaUpliftPresentation BaseCoordinateSpace)
      (T : ProductFiberCoordinateJet BaseCoordinateSpace),
      P.EquivalentUnder Q T ↔
        P.WarpedBaseCompatible Q ∧
        P.FiberRadiusCompatible Q T ∧
        P.ConnectionCompatible Q T

namespace FixedChoiceStagedKaluzaConverseCore

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

/-- **Pointwise core recognition.**  One normal scalar derivation at `x`
and one compatible normal/radial-gauge representative suffice for the full
local Ricci-flat and orbit conclusion.  No patchwide normal-coordinate or
scalar-residual hypothesis is introduced. -/
theorem exists_completePointwiseCoreKaluzaRecognition
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x)
    (N : FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt K x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition K N) := by
  have hemd : N.product.fields.EMDEquations :=
    N.realized_emd_of_normalScalarDerivation H
  refine ⟨{
    scalarPotential := K.physical.maxwell.scalarRepresentative
    scalarPotential_eq := rfl
    scalarPotential_is := K.physical.maxwell.scalarRepresentative_is
    gaugePotential := N.gaugePotential
    gaugePotential_eq := rfl
    gaugePotential_is := N.gaugePotential_is
    product := N.product
    product_eq := rfl
    product_scalar_germ := N.scalar_germ
    product_potential_germ := N.potential_germ
    baseMetric_germ := N.metric_germ
    emd_equations := hemd
    intrinsic_ricciFlat := fun z ↦
      (N.product.intrinsicRicciFlatAt_iff_emd z).mpr hemd
    nonlinear_coordinate_ricciFlat := fun T z ↦
      (N.product.fields.nonlinearLocalProductCoordinateRicciFlat_iff_emd
        T z).mpr hemd
    converse_reduction := N.product.intrinsicRicciFlatAt_iff_emd
    scalar_orbit := fun psi hpsi ↦
      scalarPotential_unique_up_to_constant D.convex D.isOpen
        K.physical.maxwell.scalarRepresentative_is hpsi
    gauge_orbit := fun A' hA' ↦
      gaugePotentialOn_unique_up_to_gaugeParameter D.convex D.isOpen
        N.gaugePotential_is hA'
    positive_coupling_orientation :=
      kaluzaCoupling_has_positive_orientation M.coupling (by
        unfold IsKaluzaCoupling
        rw [K.coupling_eq, Real.sq_sqrt (by norm_num)])
    presentation_orbit_complete := fun P Q T ↦
      P.equivalentUnder_iff_compatible Q T }⟩

end FixedChoiceStagedKaluzaConverseCore

/-! ## Exterior-Hodge representative -/

/-- Pointwise core representative whose Maxwell input is the exterior Hodge
equation itself.  Weighted divergence is derived by the normal Hodge bridge. -/
structure FixedChoiceCoreMinkowskiHodgeNormalGaugeRepresentativeAt
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
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    K.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  scalar_germ : product.fields.phi =ᶠ[nhds x]
    K.physical.maxwell.scalarRepresentative
  potential_germ : product.fields.potential =ᶠ[nhds x]
    fun y i ↦ gaugePotential y (coordinateDirection i)
  metric_germ : product.fields.metric =ᶠ[nhds x]
    coordinateMetricMatrixField4 g
  diagonal_eq_minkowski : product.fields.diagonal = minkowskiSign
  einstein : NormalGaugeEinsteinEquations product
  hodgeExterior :
    matrixExteriorDerivative
        (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureFirstJetOfSecondJet product.fields.A2 k)) =
      -(Real.sqrt 3) • matrixOneWedgeTwoTensor product.fields.phi1
        (coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureOfFirstJet product.fields.A1))
  scalarResidual : normalGaugeScalarEquationResidual product =
    actualMetricScalarEquationResidualCandidateAt4 g choice x

namespace FixedChoiceCoreMinkowskiHodgeNormalGaugeRepresentativeAt

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
  {x : CurvatureCoordinateSpace4}

/-- Convert exterior Hodge closure to the geometric weighted-divergence
representative used by pointwise core recognition. -/
def toDivergenceRepresentative
    (N : FixedChoiceCoreMinkowskiHodgeNormalGaugeRepresentativeAt K x) :
    FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt K x where
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
      (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
        (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k))
      N.product.fields.phi1 (Real.sqrt 3)
      (gaugeCurvatureOfFirstJet_transpose N.product.fields.A1)
      (gaugeCurvatureFirstJetOfSecondJet_transpose N.product.fields.A2)
      rfl (fun _ ↦ rfl) N.hodgeExterior
  scalarResidual := N.scalarResidual

end FixedChoiceCoreMinkowskiHodgeNormalGaugeRepresentativeAt

namespace FixedChoiceStagedKaluzaConverseCore

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

/-- Pointwise core recognition directly from the exterior Hodge equation. -/
theorem exists_completePointwiseCoreKaluzaRecognition_of_hodgeExterior
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x)
    (N : FixedChoiceCoreMinkowskiHodgeNormalGaugeRepresentativeAt K x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition K
      N.toDivergenceRepresentative) :=
  K.exists_completePointwiseCoreKaluzaRecognition H
    N.toDivergenceRepresentative

end FixedChoiceStagedKaluzaConverseCore

/-! ## Positive-cosine detector-channel corollaries -/

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 x : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- Positive-cosine detector channels first construct the pre-scalar core;
one normal derivation and one divergence representative at `x` then give the
complete pointwise recognition output. -/
theorem exists_completePointwiseCoreKaluzaRecognition_positiveCosineDetectorChannels
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ y ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent y ≠ -Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (H : FixedChoiceNormalEMDScalarDerivationAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x)
    (N : FixedChoiceCoreMinkowskiNormalGaugeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) N) :=
  FixedChoiceStagedKaluzaConverseCore.exists_completePointwiseCoreKaluzaRecognition
    (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric) H N

/-- Stronger positive-cosine endpoint with the representative's weighted
Maxwell divergence derived internally from exterior Hodge closure. -/
theorem exists_completePointwiseCoreKaluzaRecognition_positiveCosineDetectorChannels_of_hodgeExterior
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ y ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent y ≠ -Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (H : FixedChoiceNormalEMDScalarDerivationAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x)
    (N : FixedChoiceCoreMinkowskiHodgeNormalGaugeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric)
      N.toDivergenceRepresentative) :=
  FixedChoiceStagedKaluzaConverseCore.exists_completePointwiseCoreKaluzaRecognition_of_hodgeExterior
    (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric) H N

end RainichKaluza
