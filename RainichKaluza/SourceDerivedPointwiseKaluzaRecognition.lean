import RainichKaluza.PointwiseCoreKaluzaRecognition
import RainichKaluza.NormalEinsteinEquationBridge
import RainichKaluza.CoreNormalScalarDerivation

/-!
# Pointwise recognition with the Einstein block derived from the source

The earlier pointwise endpoint stores the normal Einstein block in its
representative.  Here that field is replaced by three literal jet/value
identifications.  The neighborhood Einstein/source identity already present
in `FixedChoiceNormalEMDScalarDerivationAt` is then transported to the
product's normal second jet and trace-reversed, so all three EMD equation
blocks are consequences rather than fields of the representative.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

/-- A compatible normal/radial-gauge representative carrying no Einstein,
weighted-Maxwell, or scalar equation as an assumption.  The Hodge exterior
law is geometric input; the scalar residual is derived later from the normal
matter-jet package.  The metric second jet, scalar covector, and
normalized Maxwell value are all derived below from the three germ
identifications rather than stored as extra alignment assumptions. -/
structure FixedChoiceCoreSourceDerivedHodgeRepresentativeAt
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
  hodgeExterior :
    matrixExteriorDerivative
        (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureFirstJetOfSecondJet product.fields.A2 k)) =
      -(Real.sqrt 3) • matrixOneWedgeTwoTensor product.fields.phi1
        (coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureOfFirstJet product.fields.A1))

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

/-- The metric germ transfers the actual second coordinate jet to the
genuine `C²` product field. -/
theorem metricSecondJet
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x) :
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

/-- The scalar germ and the core's literal scalar-potential derivative force
the product first scalar jet to be the detector covector. -/
theorem scalarCovector
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x) :
    actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus x = N.product.fields.phi1 := by
  have hderiv : fderiv ℝ N.product.fields.phi x =
      fderiv ℝ K.physical.maxwell.scalarRepresentative x :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) N.scalar_germ
  funext sigma
  symm
  calc
    N.product.fields.phi1 sigma =
        fderiv ℝ N.product.fields.phi x
          (coordinateDirection sigma) := rfl
    _ = fderiv ℝ K.physical.maxwell.scalarRepresentative x
          (coordinateDirection sigma) := by rw [hderiv]
    _ = oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus x) (coordinateDirection sigma) := by
      rw [(K.scalarPotential_matches_metric x N.point_mem).fderiv]
    _ = actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus x sigma := by
      rw [oneForm4ContinuousLinearMap_coordinateDirection]

/-- The compatible potential germ has curvature equal to the convention
physical Maxwell matrix stored by the core. -/
theorem gaugeCurvature_eq_conventionMaxwell
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x) :
    gaugeCurvatureOfFirstJet N.product.fields.A1 =
      K.conventionPhysicalMaxwellMatrix4 x := by
  have hAdiff : DifferentiableAt ℝ N.gaugePotential x :=
    (N.gaugePotential_is.1 x N.point_mem).differentiableAt
      (K.conventionMaxwell_closed.isOpen.mem_nhds N.point_mem)
  have hcomponent : ∀ mu,
      (fun y ↦ N.product.fields.potential y mu) =ᶠ[nhds x]
        (fun y ↦ N.gaugePotential y (coordinateDirection mu)) := by
    intro mu
    filter_upwards [N.potential_germ] with y hy
    exact congrFun hy mu
  have hderiv : ∀ mu,
      fderiv ℝ (fun y ↦ N.product.fields.potential y mu) x =
        fderiv ℝ (fun y ↦
          N.gaugePotential y (coordinateDirection mu)) x := by
    intro mu
    exact (hcomponent mu).fderiv_eq
  have heval : ∀ sigma mu,
      fderiv ℝ (fun y ↦
          N.gaugePotential y (coordinateDirection mu)) x
          (coordinateDirection sigma) =
        fderiv ℝ N.gaugePotential x (coordinateDirection sigma)
          (coordinateDirection mu) := by
    intro sigma mu
    rw [fderiv_clm_apply hAdiff (by fun_prop)]
    simp
  ext i j
  change N.product.fields.A1 i j - N.product.fields.A1 j i = _
  rw [show N.product.fields.A1 i j =
      fderiv ℝ (fun y ↦ N.product.fields.potential y j) x
        (coordinateDirection i) by rfl,
    show N.product.fields.A1 j i =
      fderiv ℝ (fun y ↦ N.product.fields.potential y i) x
        (coordinateDirection j) by rfl,
    hderiv j, hderiv i, heval i j, heval j i]
  exact N.gaugePotential_is.2 x N.point_mem
    (coordinateDirection i) (coordinateDirection j)

/-- Consequently the curvature-normalized Maxwell value has exactly the
Kaluza `exp(sqrt 3 phi / 2) / sqrt 2` normalization. -/
theorem normalizedMaxwellValue
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x) :
    K.curvatureNormalizedPhysicalMaxwellMatrix4 x =
      (Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
        Real.sqrt 2) • gaugeCurvatureOfFirstJet N.product.fields.A1 := by
  rw [N.gaugeCurvature_eq_conventionMaxwell]
  unfold FixedChoiceStagedKaluzaConverseCore.curvatureNormalizedPhysicalMaxwellMatrix4
    positiveEMDWeight
  have hphi : N.product.fields.phi0 =
      K.physical.maxwell.scalarRepresentative x :=
    N.scalar_germ.self_of_nhds
  rw [K.coupling_eq, hphi]
  congr 2
  ring_nf

/-- The scalar germ identifies the product Hessian with the literal scalar
covector jet used by the normal Noether package. -/
theorem phi2_eq_normalMatterScalarJet
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x) :
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

private theorem normalTwoFormSq_smul_sourceDerived
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

private theorem normalFrameMaxwellNormSq_minkowski_eq_sourceDerived
    (A1 : Fin 4 → Fin 4 → ℝ) :
    normalFrameMaxwellNormSq minkowskiSign A1 =
      normalTwoFormSq (gaugeCurvatureOfFirstJet A1) := by
  simp [normalFrameMaxwellNormSq, normalTwoFormSq,
    normalRaisedTwoForm, gaugeCurvatureOfFirstJet,
    minkowskiSign, Fin.sum_univ_succ]
  all_goals ring

private theorem normalFrameScalarBox_minkowski_eq_sourceDerived
    (Dphi : Fin 4 → OneForm4) :
    normalFrameScalarBox minkowskiSign Dphi =
      normalScalarWaveTrace Dphi := by
  simp [normalFrameScalarBox, normalScalarWaveTrace,
    normalRaisedOneForm, minkowskiSign, Fin.sum_univ_succ]

/-- The normal scalar residual is also derived from the matter-jet package;
it is not an equation or alignment field of the representative. -/
theorem derivedScalarResidual
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x) :
    normalGaugeScalarEquationResidual N.product =
      actualMetricScalarEquationResidualCandidateAt4 g choice x := by
  have hscale :
      (Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
          Real.sqrt 2) ^ 2 =
        Real.exp (Real.sqrt 3 * N.product.fields.phi0) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [H.metricResidual_eq_normal]
  unfold normalGaugeScalarEquationResidual
  rw [N.diagonal_eq_minkowski, N.phi2_eq_normalMatterScalarJet H]
  change
    normalFrameScalarBox minkowskiSign H.scalarJet -
        Real.sqrt 3 / 4 *
          Real.exp (Real.sqrt 3 * N.product.fields.phi0) *
            normalFrameMaxwellNormSq minkowskiSign
              N.product.fields.A1 =
      normalScalarEquationResidual H.scalarJet
        (K.curvatureNormalizedPhysicalMaxwellMatrix4 x) M.coupling
  rw [normalFrameScalarBox_minkowski_eq_sourceDerived,
    normalFrameMaxwellNormSq_minkowski_eq_sourceDerived]
  unfold normalScalarEquationResidual
  rw [K.coupling_eq, N.normalizedMaxwellValue,
    normalTwoFormSq_smul_sourceDerived, hscale]
  ring

/-- The actual Einstein/source identity from the scalar-derivation package
specializes to the product's normal-coordinate jet. -/
theorem productEinsteinSource
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x) :
    (fun i j ↦ coordinateEinsteinCovariant
      minkowskiMetric minkowskiMetric 0 N.product.fields.g2 i j) =
    coordinateMatterEinsteinStressCovariant4
      minkowskiMetric minkowskiMetric N.product.fields.phi1
      ((Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
        Real.sqrt 2) • gaugeCurvatureOfFirstJet N.product.fields.A1) := by
  have hactual := H.einsteinSourceNear.eq_of_nhds
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
      rw [H.metricValue, H.metricFirstJet, N.metricSecondJet, hinv]
      rfl
    _ = actualCoordinateMatterEinsteinStressCovariantField4 g
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus)
        K.curvatureNormalizedPhysicalMaxwellMatrix4 x := hactual
    _ = coordinateMatterEinsteinStressCovariant4
        minkowskiMetric minkowskiMetric N.product.fields.phi1
        ((Real.exp (Real.sqrt 3 * N.product.fields.phi0 / 2) /
          Real.sqrt 2) • gaugeCurvatureOfFirstJet
            N.product.fields.A1) := by
      unfold actualCoordinateMatterEinsteinStressCovariantField4
      rw [H.metricValue, hinv, N.scalarCovector,
        N.normalizedMaxwellValue]

/-- Exact trace reversal derives the complete normal Einstein block. -/
theorem einstein
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x) :
    NormalGaugeEinsteinEquations N.product := by
  intro n p
  rw [N.diagonal_eq_minkowski]
  exact conventionEinsteinEquationResidual_minkowski_eq_zero_of_einsteinSource
    N.product.fields.phi0 N.product.fields.phi1
      N.product.fields.A1 N.product.fields.g2
      (N.productEinsteinSource H) n p

/-- Convert to the established pointwise Hodge representative.  Its Einstein
field is filled by the source calculation above rather than assumed. -/
def toHodgeRepresentative
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x) :
    FixedChoiceCoreMinkowskiHodgeNormalGaugeRepresentativeAt K x where
  point_mem := N.point_mem
  gaugePotential := N.gaugePotential
  gaugePotential_is := N.gaugePotential_is
  product := N.product
  scalar_germ := N.scalar_germ
  potential_germ := N.potential_germ
  metric_germ := N.metric_germ
  diagonal_eq_minkowski := N.diagonal_eq_minkowski
  einstein := N.einstein H
  hodgeExterior := N.hodgeExterior
  scalarResidual := N.derivedScalarResidual H

end FixedChoiceCoreSourceDerivedHodgeRepresentativeAt

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

/-- **Source-derived pointwise Kaluza recognition.**  The normal Einstein
equation follows from the staged neighborhood source identity, the weighted
Maxwell equation follows from exterior Hodge closure, and the scalar equation
follows from contracted Bianchi/Noether.  The returned actual local product
is intrinsically Ricci-flat and remains Ricci-flat in every supported
nonlinear uplift chart. -/
theorem exists_completeSourceDerivedPointwiseKaluzaRecognition
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (H : FixedChoiceNormalEMDScalarDerivationAt K x)
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition K
      (N.toHodgeRepresentative H).toDivergenceRepresentative) :=
  K.exists_completePointwiseCoreKaluzaRecognition_of_hodgeExterior H
    (N.toHodgeRepresentative H)

/-- Stronger endpoint in which the staged core itself supplies the
neighborhood Einstein/source identity.  The normal matter-jet package no
longer stores that equation. -/
theorem exists_completeSourceDerivedPointwiseKaluzaRecognition_of_coreEntrance
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (H : FixedChoiceNormalMatterJetDerivationAt K x)
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition K
      (N.toHodgeRepresentative
        (H.withCoreEinsteinSource halign N.point_mem)).toDivergenceRepresentative) :=
  K.exists_completeSourceDerivedPointwiseKaluzaRecognition
    (H.withCoreEinsteinSource halign N.point_mem) N

end FixedChoiceStagedKaluzaConverseCore

/-! ## Detector-channel endpoint -/

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 x : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- **Strongest compiled fixed-chart recognition theorem.**  Persistent
detector channels build the scalar-residual-free positive-cosine core.  The
core entrance supplies the Einstein/source equation, exterior Hodge closure
supplies weighted Maxwell, and contracted Bianchi/Noether supplies the scalar
equation.  The conclusion is a genuine `C²` Ricci-flat Kaluza product germ,
with intrinsic, nonlinear-chart, converse, and orbit statements. -/
theorem exists_completeSourceDerivedPointwiseKaluzaRecognition_positiveCosineDetectorChannels
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
    (H : FixedChoiceNormalMatterJetDerivationAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x)
    (N : FixedChoiceCoreSourceDerivedHodgeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric)
      (N.toHodgeRepresentative
        (H.withCoreEinsteinSource
          (FixedChoiceStagedKaluzaConverseBoundary.ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch_seedAlignment
            D hchart)
          N.point_mem)).toDivergenceRepresentative) :=
  FixedChoiceStagedKaluzaConverseCore.exists_completeSourceDerivedPointwiseKaluzaRecognition_of_coreEntrance
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric)
      (FixedChoiceStagedKaluzaConverseBoundary.ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch_seedAlignment
        D hchart) H N

end RainichKaluza
