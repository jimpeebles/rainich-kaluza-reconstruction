import RainichKaluza.CoreSourceDerivedHodgeBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Scalar-residual alignment for a source-derived normal representative

The source-derived pointwise endpoint previously retained an equality between
the product's normal scalar residual and the detector's metric residual as a
field of its representative.  This file derives that equality from the
scalar germ and the normal matter-jet package.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

namespace FixedChoiceCoreSourceDerivedHodgeRepresentativeAt

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

/-- The scalar germ and the core's literal first derivative identify the
product Hessian with the scalar covector jet used by the normal Noether
package. -/
theorem phi2_eq_scalarJet
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalMatterJetDerivationAt K x) :
    N.product.fields.phi2 = H.scalarJet := by
  funext r s
  let p : CurvatureCoordinateSpace4 → ℝ := N.product.fields.phi
  let phi : CurvatureCoordinateSpace4 → ℝ :=
    K.physical.maxwell.scalarRepresentative
  let vcomp : CurvatureCoordinateSpace4 → ℝ := fun y ↦
    actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus y s
  have hfirst : fderiv ℝ p =ᶠ[nhds x] fderiv ℝ phi :=
    N.scalar_germ.fderiv
  have heval :
      (fun y ↦ fderiv ℝ p y (coordinateDirection s)) =ᶠ[nhds x]
        (fun y ↦ fderiv ℝ phi y (coordinateDirection s)) := by
    filter_upwards [hfirst] with y hy
    rw [hy]
  have hpotential :
      (fun y ↦ fderiv ℝ phi y (coordinateDirection s)) =ᶠ[nhds x]
        vcomp := by
    filter_upwards [D.isOpen.mem_nhds N.point_mem] with y hy
    calc
      fderiv ℝ phi y (coordinateDirection s) =
          oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) (coordinateDirection s) := by
        rw [(K.scalarPotential_matches_metric y hy).fderiv]
      _ = vcomp y := by
        rw [oneForm4ContinuousLinearMap_coordinateDirection]
  have hcomponent := heval.trans hpotential
  have hpDiff : DifferentiableAt ℝ (fderiv ℝ p) x :=
    ((N.product.fields.phi_contDiffAt.fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hderiv := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hcomponent
  calc
    N.product.fields.phi2 r s =
        fderiv ℝ (fun y ↦ fderiv ℝ p y (coordinateDirection s)) x
          (coordinateDirection r) := by
      unfold KaluzaNormalGaugeFieldsAt.phi2 p
      change
        fderiv ℝ (fderiv ℝ N.product.fields.phi) x
            (coordinateDirection r) (coordinateDirection s) =
          fderiv ℝ (fun y ↦
            fderiv ℝ p y (coordinateDirection s)) x
              (coordinateDirection r)
      rw [fderiv_clm_apply hpDiff (by fun_prop)]
      simp [p]
    _ = scalarFieldCoordinateFDeriv vcomp x r := by
      unfold scalarFieldCoordinateFDeriv
      rw [show curvatureCoordinateDirection r = coordinateDirection r by
        rfl]
      rw [hderiv]
    _ = H.scalarJet r s := H.scalarFirstJet r s

private theorem normalTwoFormSq_smul
    (c : ℝ) (F : Matrix4) :
    normalTwoFormSq (c • F) = c ^ 2 * normalTwoFormSq F := by
  unfold normalTwoFormSq normalRaisedTwoForm
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem normalFrameMaxwellNormSq_minkowski_eq
    (A1 : Fin 4 → Fin 4 → ℝ) :
    normalFrameMaxwellNormSq minkowskiSign A1 =
      normalTwoFormSq (gaugeCurvatureOfFirstJet A1) := by
  simp [normalFrameMaxwellNormSq, normalTwoFormSq,
    normalRaisedTwoForm, gaugeCurvatureOfFirstJet,
    minkowskiSign, Fin.sum_univ_succ]
  all_goals ring

private theorem normalFrameScalarBox_minkowski_eq
    (Dphi : Fin 4 → OneForm4) :
    normalFrameScalarBox minkowskiSign Dphi =
      normalScalarWaveTrace Dphi := by
  simp [normalFrameScalarBox, normalScalarWaveTrace,
    normalRaisedOneForm, minkowskiSign, Fin.sum_univ_succ]

/-- The scalar residual stored by the Kaluza normal-gauge backend is the
normal Noether residual of the core's curvature-normalized Maxwell field. -/
theorem normalGaugeScalarEquationResidual_eq_normalMatterResidual
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalMatterJetDerivationAt K x) :
    normalGaugeScalarEquationResidual N.product =
      normalScalarEquationResidual H.scalarJet
        (K.curvatureNormalizedPhysicalMaxwellMatrix4 x) M.coupling := by
  have hscale :
      (Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
          Real.sqrt 2) ^ 2 =
        Real.exp (Real.sqrt 3 * N.product.fields.phi0) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold normalGaugeScalarEquationResidual
  rw [N.diagonal_eq_minkowski, N.phi2_eq_scalarJet H]
  change
    normalFrameScalarBox minkowskiSign H.scalarJet -
        Real.sqrt 3 / 4 *
          Real.exp (Real.sqrt 3 * N.product.fields.phi0) *
            normalFrameMaxwellNormSq minkowskiSign
              N.product.fields.A1 =
      normalScalarEquationResidual H.scalarJet
        (K.curvatureNormalizedPhysicalMaxwellMatrix4 x) M.coupling
  rw [normalFrameScalarBox_minkowski_eq,
    normalFrameMaxwellNormSq_minkowski_eq]
  unfold normalScalarEquationResidual
  rw [K.coupling_eq, N.normalizedMaxwellValue,
    normalTwoFormSq_smul, hscale]
  ring

/-- Hence the normal representative's scalar residual equals the literal
metric detector residual; no representative residual field is required. -/
theorem scalarResidual_of_normalMatterJet
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalMatterJetDerivationAt K x) :
    normalGaugeScalarEquationResidual N.product =
      actualMetricScalarEquationResidualCandidateAt4 g choice x := by
  rw [N.normalGaugeScalarEquationResidual_eq_normalMatterResidual H]
  exact H.metricResidual_eq_normal.symm

end FixedChoiceCoreSourceDerivedHodgeRepresentativeAt

end RainichKaluza
