import RainichKaluza.StagedHodgeExteriorBridge
import RainichKaluza.NormalEinsteinEquationBridge

/-!
# Staged Einstein entrance to the normal Kaluza backend

This module transports the literal Einstein/source identity already proved
for the recognized metric into the genuine second jet of a compatible
normal/radial-gauge product germ.  It then applies the exact four-dimensional
trace-reversal and Maxwell-normalization bridge, deriving the complete
normal-gauge Einstein block used by the Kaluza Ricci reduction.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

namespace FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt

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

/-- Germ equality with a genuine `C²` product representative identifies its
literal metric second jet with the actual coordinate second jet. -/
theorem coordinateMetric_secondJet_eq_product
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x) :
    actualCoordinateMetricJet2Field4 g x = N.product.fields.g2 := by
  funext r s i j
  let pcomp : CurvatureCoordinateSpace4 → ℝ :=
    fun y ↦ N.product.fields.metric y i j
  let gcomp : CurvatureCoordinateSpace4 → ℝ :=
    fun y ↦ coordinateMetricMatrixField4 g y i j
  have hcomp : pcomp =ᶠ[nhds x] gcomp := by
    filter_upwards [N.metric_germ] with y hy
    exact congrFun (congrFun hy i) j
  have hfirst : fderiv ℝ pcomp =ᶠ[nhds x] fderiv ℝ gcomp :=
    hcomp.fderiv
  have heval :
      (fun y ↦ fderiv ℝ pcomp y (coordinateDirection s)) =ᶠ[nhds x]
        (fun y ↦ fderiv ℝ gcomp y (coordinateDirection s)) := by
    filter_upwards [hfirst] with y hy
    rw [hy]
  have hpDiff : DifferentiableAt ℝ (fderiv ℝ pcomp) x := by
    exact (((N.product.fields.metric_contDiffAt i j).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hsecond := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heval
  unfold actualCoordinateMetricJet2Field4 actualCoordinateMetricJet1Field4
    scalarFieldCoordinateFDeriv KaluzaNormalGaugeFieldsAt.g2
  change fderiv ℝ (fun y ↦ fderiv ℝ gcomp y
      (coordinateDirection s)) x (coordinateDirection r) =
    fderiv ℝ (fderiv ℝ pcomp) x
      (coordinateDirection r) (coordinateDirection s)
  rw [← hsecond]
  rw [fderiv_clm_apply hpDiff (by fun_prop)]
  simp

/-- The staged curvature-normalized Maxwell value becomes exactly the
normalization of the curvature of the product representative's potential. -/
theorem curvatureNormalizedMaxwell_eq_productGaugeCurvature
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x) :
    stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B x =
      (Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
        Real.sqrt 2) • gaugeCurvatureOfFirstJet N.product.fields.A1 := by
  rw [N.gaugeCurvature_eq_stagedConventionMaxwell]
  unfold stagedCurvatureNormalizedPhysicalMaxwellMatrix4
    positiveEMDWeight
  rw [B.coupling_eq, N.phi0_eq_scalarRepresentative]
  congr 2
  ring_nf

/-- The actual-coordinate Einstein/source identity specializes to the
literal normal-coordinate second jet of the compatible product germ. -/
theorem productEinsteinSource
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    (fun i j ↦ coordinateEinsteinCovariant
      minkowskiMetric minkowskiMetric 0 N.product.fields.g2 i j) =
    coordinateMatterEinsteinStressCovariant4
      minkowskiMetric minkowskiMetric N.product.fields.phi1
      ((Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
        Real.sqrt 2) • gaugeCurvatureOfFirstJet N.product.fields.A1) := by
  have hactual := B.actualCoordinateEinsteinField4_eq_actualMatterSource
    halign x N.point_mem
  have hg0 := N.coordinateMetric_eq_minkowski
  have hg1 : actualCoordinateMetricJet1Field4 g x = 0 := by
    funext r i j
    exact N.coordinateMetric_firstJet_eq_zero r i j
  have hg2 := N.coordinateMetric_secondJet_eq_product
  have hv := N.phi1_eq_actualMetricScalarOneForm
  have hF := N.curvatureNormalizedMaxwell_eq_productGaugeCurvature
  have hinv : (minkowskiMetric⁻¹ : Matrix4) = minkowskiMetric :=
    Matrix.inv_eq_right_inv minkowskiMetric_sq
  calc
    (fun i j ↦ coordinateEinsteinCovariant
        minkowskiMetric minkowskiMetric 0 N.product.fields.g2 i j) =
        actualCoordinateEinsteinField4 g x := by
      ext i j
      simp only [actualCoordinateEinsteinField4,
        actualCoordinateScalarCurvatureField4,
        actualCoordinateRicciCovariantField4]
      rw [hg0, hg1, hg2, hinv]
      rfl
    _ = actualCoordinateMatterEinsteinStressCovariantField4 g
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus)
        (stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B) x := hactual
    _ = coordinateMatterEinsteinStressCovariant4
        minkowskiMetric minkowskiMetric N.product.fields.phi1
        ((Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
          Real.sqrt 2) • gaugeCurvatureOfFirstJet
            N.product.fields.A1) := by
      unfold actualCoordinateMatterEinsteinStressCovariantField4
      rw [hg0, hinv, ← hv, hF]

/-- **The normal Einstein block is derived, not assumed.**  Persistent
detector entrance gives the actual Einstein/source identity; compatible
metric, scalar, and gauge germs transfer it to the product jet; and exact
trace reversal gives the backend equation with all Kaluza factors fixed. -/
theorem einstein_of_stagedSource
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    NormalGaugeEinsteinEquations N.product := by
  intro n p
  rw [N.diagonal_eq_minkowski]
  exact conventionEinsteinEquationResidual_minkowski_eq_zero_of_einsteinSource
    N.product.fields.phi0 N.product.fields.phi1
      N.product.fields.A1 N.product.fields.g2
      (N.productEinsteinSource halign) n p

end FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt

end RainichKaluza
