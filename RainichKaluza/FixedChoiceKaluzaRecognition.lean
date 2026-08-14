import RainichKaluza.StagedKaluzaConverse
import RainichKaluza.ConditionalKaluzaUplift

/-!
# Fixed-choice local Kaluza recognition and uplift

`StagedKaluzaConverse` reaches a genuine scalar potential, both Maxwell
exterior equations, the convention-normalized Maxwell field and gauge
potential, and the algebraic Ricci entrance.  This file isolates the exact
remaining bridge into the existing actual `C^2` normal/radial-gauge Kaluza
backend.

The bridge does not re-assume the scalar equation.  Instead it identifies the
normal-frame scalar residual of the realized fields with the literal
metric-constructed residual retained by the staged boundary.  Its vanishing
then follows from that boundary.  The only equation hypotheses still stated
at the realization layer are the normal-frame Einstein and weighted Maxwell
blocks.  Proving those two blocks from the entrance stress identity and the
closed weighted Hodge flux is the remaining geometric source/field splice.

The returned local-product germ retains an eventual equality between its base
metric and the metric being recognized.  Consequently the result is an
uplift of the supplied metric germ, rather than merely an unrelated Ricci-flat
Kaluza germ with isomorphic field data.
-/

namespace RainichKaluza

open Set Filter
open scoped Topology

/-! ## Split normal-frame equation predicates -/

/-- Einstein block of the convention-fixed normal-frame EMD equations. -/
noncomputable def NormalGaugeEinsteinEquations
    {x : BaseCoordinateSpace}
    (K : LorentzianKaluzaLocalProductGermAt x) : Prop :=
  ∀ n p : Fin 4,
    conventionEinsteinEquationResidual K.fields.phi0 K.fields.diagonal
      K.fields.phi1 K.fields.A1 K.fields.g2 n p = 0

/-- Weighted Maxwell block of the convention-fixed normal-frame EMD
equations. -/
noncomputable def NormalGaugeWeightedMaxwellEquations
    {x : BaseCoordinateSpace}
    (K : LorentzianKaluzaLocalProductGermAt x) : Prop :=
  ∀ n : Fin 4,
    conventionWeightedMaxwellResidual K.fields.diagonal K.fields.phi1
      K.fields.A1 K.fields.A2 n = 0

/-- Scalar residual of the convention-fixed normal-frame realization. -/
noncomputable def normalGaugeScalarEquationResidual
    {x : BaseCoordinateSpace}
    (K : LorentzianKaluzaLocalProductGermAt x) : ℝ :=
  conventionScalarEquationResidual K.fields.phi0 K.fields.diagonal
    K.fields.phi2 K.fields.A1

/-- The backend's `EMDEquations` package is exactly the three displayed
normal-frame blocks. -/
theorem lorentzianKaluza_emDEquations_iff
    {x : BaseCoordinateSpace}
    (K : LorentzianKaluzaLocalProductGermAt x) :
    K.fields.EMDEquations ↔
      NormalGaugeEinsteinEquations K ∧
        NormalGaugeWeightedMaxwellEquations K ∧
          normalGaugeScalarEquationResidual K = 0 := by
  rfl

/-! ## One honest normal/radial-gauge representative -/

/-- One actual-field representative completing a staged fixed-choice
boundary.

This is intentionally existential data, not a function accepting every
differentiable scalar or gauge potential.  A general `IsGaugePotentialOn`
witness is only `C^1`; demanding a `C^2` Kaluza field equal to every such
witness would silently strengthen its regularity.  Here one gauge potential
is supplied together with one `C^2` normal/radial-gauge product germ, and the
three reconstructed fields are identified only as germs at the base point.

The returned `LorentzianKaluzaLocalProductGermAt` supplies componentwise
`C^2` regularity, eventual metric symmetry, normal coordinates, radial gauge,
nondegeneracy, and the displayed Lorentz signature without duplication.
Only the Einstein and weighted-Maxwell blocks remain zero hypotheses.  The
scalar block is an equality with the staged metric residual. -/
structure FixedChoiceNormalGaugeRepresentativeAt
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
  einstein : NormalGaugeEinsteinEquations product
  weightedMaxwell : NormalGaugeWeightedMaxwellEquations product
  scalarResidual : normalGaugeScalarEquationResidual product =
    actualMetricScalarEquationResidualCandidateAt4 g choice x

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

/-- The scalar potential already contained in the staged boundary makes the
selected Phase-III scalar branch closed. -/
theorem scalarOneForm_closed
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch) :
    IsClosedScalarOneFormOn (C.branchScalarOneForm branch) U := by
  have hpotential : C.BranchScalarPotentialExists branch :=
    ⟨B.physical.maxwell.scalarRepresentative,
      B.physical.maxwell.scalarRepresentative_is⟩
  cases branch with
  | plus =>
      exact (C.plusField_closed_iff D.isOpen).mpr
        ((C.plusScalarPotentialExists_iff_curvatureBranchCloses
          D.convex D.isOpen).mp hpotential)
  | minus =>
      exact (C.minusField_closed_iff D.isOpen).mpr
        ((C.minusScalarPotentialExists_iff_curvatureBranchCloses
          D.convex D.isOpen).mp hpotential)

/-- The fixed positive coupling stored by either half-angle chart is a
Kaluza coupling. -/
theorem coupling_is_kaluza
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch) :
    IsKaluzaCoupling M.coupling := by
  unfold IsKaluzaCoupling
  rw [B.coupling_eq, Real.sq_sqrt (by norm_num)]

/-- The supplied representative satisfies the full EMD package because its
scalar residual is the staged metric residual, already zero. -/
theorem realized_emd
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (N : FixedChoiceNormalGaugeRepresentativeAt B x) :
    N.product.fields.EMDEquations := by
  rw [lorentzianKaluza_emDEquations_iff]
  refine ⟨N.einstein, N.weightedMaxwell, ?_⟩
  rw [N.scalarResidual]
  exact B.scalarResidual_zero x N.point_mem

end FixedChoiceStagedKaluzaConverseBoundary

/-! ## Complete recognition output -/

/-- Complete local recognition output for the supplied normal/radial-gauge
representative.  It retains the reconstructed scalar and convention Maxwell
potential, the original base metric germ, intrinsic and explicit nonlinear-
coordinate Ricci flatness, the converse EMD reduction, and the established
scalar/gauge/coupling/presentation orbits. -/
structure CompleteFixedChoiceKaluzaRecognition
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
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (N : FixedChoiceNormalGaugeRepresentativeAt B x) where
  scalarPotential : CurvatureCoordinateSpace4 → ℝ
  scalarPotential_eq : scalarPotential =
    B.physical.maxwell.scalarRepresentative
  scalarPotential_is : IsScalarPotentialOn scalarPotential
    (C.branchScalarOneForm branch) U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_eq : gaugePotential = N.gaugePotential
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    B.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  product_eq : product = N.product
  product_scalar_germ : product.fields.phi =ᶠ[𝓝 x] scalarPotential
  product_potential_germ : product.fields.potential =ᶠ[𝓝 x]
    fun y i => gaugePotential y (coordinateDirection i)
  baseMetric_germ : product.fields.metric =ᶠ[𝓝 x]
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
      ∃ c : ℝ, U.EqOn scalarPotential (fun y => psi y + c)
  gauge_orbit :
    ∀ A' : CurvatureCoordinateSpace4 →
        CurvatureCoordinateSpace4 →L[ℝ] ℝ,
      IsGaugePotentialOn A'
        B.physical.maxwell.conventionNormalizedPhysicalMaxwell U →
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

/-- **Full fixed-choice local recognition/uplift theorem.**  A staged
boundary plus one compatible `C^2` normal/radial-gauge representative
produces a circle-invariant Lorentzian Kaluza metric that is intrinsically
Ricci-flat in every nonlinear chart, retains the full converse reduction and
orbit package, and has the original metric as its base metric germ. -/
theorem exists_completeFixedChoiceKaluzaRecognition
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (N : FixedChoiceNormalGaugeRepresentativeAt B x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition B N) := by
  have hemd : N.product.fields.EMDEquations := B.realized_emd N
  refine ⟨{
    scalarPotential := B.physical.maxwell.scalarRepresentative
    scalarPotential_eq := rfl
    scalarPotential_is := B.physical.maxwell.scalarRepresentative_is
    gaugePotential := N.gaugePotential
    gaugePotential_eq := rfl
    gaugePotential_is := N.gaugePotential_is
    product := N.product
    product_eq := rfl
    product_scalar_germ := N.scalar_germ
    product_potential_germ := N.potential_germ
    baseMetric_germ := N.metric_germ
    emd_equations := hemd
    intrinsic_ricciFlat := fun z =>
      (N.product.intrinsicRicciFlatAt_iff_emd z).mpr hemd
    nonlinear_coordinate_ricciFlat := fun T z =>
      (N.product.fields.nonlinearLocalProductCoordinateRicciFlat_iff_emd
        T z).mpr hemd
    converse_reduction := N.product.intrinsicRicciFlatAt_iff_emd
    scalar_orbit := fun psi hpsi =>
      scalarPotential_unique_up_to_constant D.convex D.isOpen
        B.physical.maxwell.scalarRepresentative_is hpsi
    gauge_orbit := fun A' hA' =>
      gaugePotentialOn_unique_up_to_gaugeParameter D.convex D.isOpen
        N.gaugePotential_is hA'
    positive_coupling_orientation :=
      kaluzaCoupling_has_positive_orientation M.coupling
        B.coupling_is_kaluza
    presentation_orbit_complete := fun P Q T =>
      P.equivalentUnder_iff_compatible Q T }⟩

end FixedChoiceStagedKaluzaConverseBoundary

end RainichKaluza
