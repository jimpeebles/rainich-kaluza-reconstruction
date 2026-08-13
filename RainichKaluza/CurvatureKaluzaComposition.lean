import RainichKaluza.CurvatureBranchIntegration
import RainichKaluza.ConditionalKaluzaUplift

/-!
# Curvature-to-Kaluza branch composition

This file is the first complete composition layer across the curvature scalar
classifier, the Phase-III Maxwell obstruction test, and the conditional
five-dimensional uplift theorem.

For either relative-sign scalar branch it returns exactly one of three
evidence-bearing results:

* a scalar rejection, with a point where the curvature closure matrix is
  nonzero;
* a Maxwell rejection, with a surviving scalar potential and a point where
  one of the two explicit EMD obstruction three-forms is nonzero;
* Phase-III acceptance, with both a scalar potential and vanishing Maxwell
  obstructions throughout the patch.

The accepted case is deliberately not confused with a completed uplift.  It
proves the two exponential-weight closure identities at every point, then
names the remaining field-level regularity, Kaluza-coupling, and normal-gauge
realizer data needed by `AcceptedKaluzaBranchAt`.  Supplying exactly those
obligations invokes `exists_completeConditionalKaluzaUplift` without another
hidden branch, chart, or gauge choice.
-/

namespace RainichKaluza

open Set

/-- The two curvature scalar candidates after the relative-sign ambiguity. -/
inductive RelativeSignScalarBranch4 where
  | plus
  | minus
  deriving DecidableEq, Repr

namespace CurvatureScalarBranchComponentPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- Genuine scalar one-form selected by a relative-sign branch. -/
noncomputable def branchScalarOneForm
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
  match branch with
  | .plus => C.plusField
  | .minus => C.minusField

/-- Coordinate value of the selected scalar one-form. -/
def branchScalarOneFormValue
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) : OneForm4 :=
  match branch with
  | .plus => (C.jet z).vPlus
  | .minus => (C.jet z).vMinus

/-- The scalar candidate survives when it is the derivative of a genuine
local potential on the whole patch. -/
def BranchScalarPotentialExists
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) : Prop :=
  ∃ phi : CurvatureCoordinateSpace4 → ℝ,
    IsScalarPotentialOn phi (C.branchScalarOneForm branch) U

/-- Curvature closure matrix of the selected scalar branch. -/
noncomputable def branchScalarObstruction
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  match branch with
  | .plus => (C.jet z).dalpha + (C.jet z).dbeta
  | .minus => (C.jet z).dalpha - (C.jet z).dbeta

@[simp]
theorem branchScalarOneForm_plus
    (C : CurvatureScalarBranchComponentPatch4 U) :
    C.branchScalarOneForm .plus = C.plusField := rfl

@[simp]
theorem branchScalarOneForm_minus
    (C : CurvatureScalarBranchComponentPatch4 U) :
    C.branchScalarOneForm .minus = C.minusField := rfl

@[simp]
theorem branchScalarOneFormValue_plus
    (C : CurvatureScalarBranchComponentPatch4 U)
    (z : CurvatureCoordinateSpace4) :
    C.branchScalarOneFormValue .plus z = (C.jet z).vPlus := rfl

@[simp]
theorem branchScalarOneFormValue_minus
    (C : CurvatureScalarBranchComponentPatch4 U)
    (z : CurvatureCoordinateSpace4) :
    C.branchScalarOneFormValue .minus z = (C.jet z).vMinus := rfl

@[simp]
theorem branchScalarPotentialExists_plus
    (C : CurvatureScalarBranchComponentPatch4 U) :
    C.BranchScalarPotentialExists .plus ↔ C.PlusScalarPotentialExists := by
  rfl

@[simp]
theorem branchScalarPotentialExists_minus
    (C : CurvatureScalarBranchComponentPatch4 U) :
    C.BranchScalarPotentialExists .minus ↔ C.MinusScalarPotentialExists := by
  rfl

/-- A finite rejection certificate for one scalar branch. -/
structure ScalarBranchObstructionWitness
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) where
  point : CurvatureCoordinateSpace4
  point_mem : point ∈ U
  obstruction_ne : C.branchScalarObstruction branch point ≠ 0

/-- Potential existence is exactly pointwise vanishing of the selected
curvature closure matrix. -/
theorem branchScalarPotentialExists_iff_obstruction_zero_on
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    C.BranchScalarPotentialExists branch ↔
      ∀ z ∈ U, C.branchScalarObstruction branch z = 0 := by
  cases branch with
  | plus =>
      rw [branchScalarPotentialExists_plus,
        C.plusScalarPotentialExists_iff_curvatureBranchCloses hconvex hopen]
      constructor
      · intro h z hz
        have hclosed := h z hz
        change oneFormJetExteriorDerivative (C.jet z).vPlusJet = 0 at hclosed
        simpa only [branchScalarObstruction,
          CurvatureScalarBranchJet4.vPlus_exterior] using hclosed
      · intro h z hz
        change oneFormJetExteriorDerivative (C.jet z).vPlusJet = 0
        simpa only [branchScalarObstruction,
          CurvatureScalarBranchJet4.vPlus_exterior] using h z hz
  | minus =>
      rw [branchScalarPotentialExists_minus,
        C.minusScalarPotentialExists_iff_curvatureBranchCloses hconvex hopen]
      constructor
      · intro h z hz
        have hclosed := h z hz
        change oneFormJetExteriorDerivative (C.jet z).vMinusJet = 0 at hclosed
        simpa only [branchScalarObstruction,
          CurvatureScalarBranchJet4.vMinus_exterior] using hclosed
      · intro h z hz
        change oneFormJetExteriorDerivative (C.jet z).vMinusJet = 0
        simpa only [branchScalarObstruction,
          CurvatureScalarBranchJet4.vMinus_exterior] using h z hz

/-- A scalar obstruction witness rules out a potential on the whole patch. -/
theorem not_branchScalarPotentialExists_of_witness
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (w : ScalarBranchObstructionWitness C branch) :
    ¬C.BranchScalarPotentialExists branch := by
  intro hpotential
  have hzero :=
    (C.branchScalarPotentialExists_iff_obstruction_zero_on branch
      hconvex hopen).mp hpotential w.point w.point_mem
  exact w.obstruction_ne hzero

/-- Every rejected scalar branch has a finite curvature-matrix witness. -/
theorem exists_scalarBranchObstructionWitness_of_not_potential
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (hnot : ¬C.BranchScalarPotentialExists branch) :
    Nonempty (ScalarBranchObstructionWitness C branch) := by
  classical
  by_contra hwitness
  have hall : ∀ z ∈ U, C.branchScalarObstruction branch z = 0 := by
    intro z hz
    by_contra hne
    exact hwitness ⟨{
      point := z
      point_mem := hz
      obstruction_ne := hne
    }⟩
  exact hnot <|
    (C.branchScalarPotentialExists_iff_obstruction_zero_on branch
      hconvex hopen).mpr hall

end CurvatureScalarBranchComponentPatch4

/-- Smooth local data needed to evaluate the explicit positive-`q` Phase-III
Maxwell obstruction pair throughout a coordinate patch.  The scalar covector
`v` is supplied by the selected curvature branch rather than duplicated here. -/
structure PositiveQPhaseIIIPatch4
    (U : Set CurvatureCoordinateSpace4) where
  L : CurvatureCoordinateSpace4 → Matrix4
  dL : CurvatureCoordinateSpace4 → Fin 4 → Matrix4
  q : CurvatureCoordinateSpace4 → ℝ
  dq : CurvatureCoordinateSpace4 → OneForm4
  omega : CurvatureCoordinateSpace4 → OneForm4
  c : CurvatureCoordinateSpace4 → ℝ
  s : CurvatureCoordinateSpace4 → ℝ
  coupling : ℝ
  dc : CurvatureCoordinateSpace4 → OneForm4
  ds : CurvatureCoordinateSpace4 → OneForm4
  dc_eq : ∀ z ∈ U, dc z = (-(s z)) • omega z
  ds_eq : ∀ z ∈ U, ds z = c z • omega z

namespace PositiveQPhaseIIIPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- Exterior duality jet evaluated using the scalar covector of a selected
curvature branch. -/
noncomputable def exteriorJet
    (M : PositiveQPhaseIIIPatch4 U)
    (z : CurvatureCoordinateSpace4) :
    ExteriorDualityJet OneForm4 Matrix4 ThreeTensor4 :=
  localPositiveQExteriorDualityJet (M.L z) (M.dL z) (M.q z) (M.dq z)
    (M.c z) (M.s z) (M.dc z) (M.ds z)

/-- First explicit EMD obstruction channel for the selected scalar branch. -/
noncomputable def branchObstructionF
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) : ThreeTensor4 :=
  localSeedEMDObstructionF (M.exteriorJet z)
    (M.omega z) (C.branchScalarOneFormValue branch z) M.coupling

/-- Hodge-channel EMD obstruction for the selected scalar branch. -/
noncomputable def branchObstructionG
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) : ThreeTensor4 :=
  localSeedEMDObstructionG (M.exteriorJet z)
    (M.omega z) (C.branchScalarOneFormValue branch z) M.coupling

/-- Phase-III acceptance predicate: both computable obstruction tensors
vanish at every point of the patch. -/
def BranchObstructionsVanishOn
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) : Prop :=
  ∀ z ∈ U,
    M.branchObstructionF C branch z = 0 ∧
      M.branchObstructionG C branch z = 0

/-- The rescaled EMD exterior equations hold throughout the patch. -/
def BranchEMDExteriorClosureOn
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) : Prop :=
  ∀ z ∈ U,
    let J := M.exteriorJet z
    EMDExteriorClosure matrixOneWedgeTwo
      (C.branchScalarOneFormValue branch z) M.coupling
      J.rotatedF J.rotatedG
      (J.rotatedDF matrixOneWedgeTwo)
      (J.rotatedDG matrixOneWedgeTwo)

/-- A finite Phase-III rejection witness.  The disjunction records which of
the two explicit obstruction channels rejects the branch. -/
structure MaxwellBranchObstructionWitness
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) where
  point : CurvatureCoordinateSpace4
  point_mem : point ∈ U
  obstruction_ne :
    M.branchObstructionF C branch point ≠ 0 ∨
      M.branchObstructionG C branch point ≠ 0

/-- The pointwise Maxwell obstruction pair is necessary and sufficient for
the full rescaled EMD exterior equations on the selected scalar branch. -/
theorem branchEMDExteriorClosureOn_iff_obstructionsVanishOn
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) :
    M.BranchEMDExteriorClosureOn C branch ↔
      M.BranchObstructionsVanishOn C branch := by
  constructor
  · intro hemd z hz
    exact (localPositiveQ_emdClosure_iff_obstructions_zero
      (M.L z) (M.dL z) (M.q z) (M.dq z) (M.omega z)
      (C.branchScalarOneFormValue branch z) (M.c z) (M.s z) M.coupling
      (M.dc z) (M.ds z) (M.dc_eq z hz) (M.ds_eq z hz)).mp (hemd z hz)
  · intro hobs z hz
    exact (localPositiveQ_emdClosure_iff_obstructions_zero
      (M.L z) (M.dL z) (M.q z) (M.dq z) (M.omega z)
      (C.branchScalarOneFormValue branch z) (M.c z) (M.s z) M.coupling
      (M.dc z) (M.ds z) (M.dc_eq z hz) (M.ds_eq z hz)).mpr (hobs z hz)

/-- Vanishing Phase-III obstructions supply the two canonical exponential-
weight closure jets pointwise on the whole patch. -/
theorem branchObstructionsVanishOn_gives_closed_exponentialWeightJets
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hobs : M.BranchObstructionsVanishOn C branch)
    (rMinus rPlus : CurvatureCoordinateSpace4 → ℝ) :
    ∀ z ∈ U,
      let J := M.exteriorJet z
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo (rMinus z)
          (negativeEMDWeightDerivative M.coupling (rMinus z)
            (C.branchScalarOneFormValue branch z))
          J.rotatedF (J.rotatedDF matrixOneWedgeTwo) = 0 ∧
        scaledTwoFormExteriorDerivative matrixOneWedgeTwo (rPlus z)
          (positiveEMDWeightDerivative M.coupling (rPlus z)
            (C.branchScalarOneFormValue branch z))
          J.rotatedG (J.rotatedDG matrixOneWedgeTwo) = 0 := by
  intro z hz
  exact localPositiveQ_obstructions_give_closed_exponentialWeightJets
    (M.L z) (M.dL z) (M.q z) (M.dq z) (M.omega z)
    (C.branchScalarOneFormValue branch z) (M.c z) (M.s z) M.coupling
    (rMinus z) (rPlus z) (M.dc z) (M.ds z)
    (M.dc_eq z hz) (M.ds_eq z hz) (hobs z hz)

/-- The explicit obstruction test either accepts the entire patch or returns
a point and a named nonzero channel. -/
theorem obstructionsVanishOn_or_maxwellWitness
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) :
    M.BranchObstructionsVanishOn C branch ∨
      Nonempty (MaxwellBranchObstructionWitness M C branch) := by
  classical
  by_cases hobs : M.BranchObstructionsVanishOn C branch
  · exact Or.inl hobs
  · right
    have hexists : ∃ z, ∃ _ : z ∈ U,
        ¬(M.branchObstructionF C branch z = 0 ∧
          M.branchObstructionG C branch z = 0) := by
      simpa only [BranchObstructionsVanishOn, not_forall] using hobs
    obtain ⟨z, hz, hpair⟩ := hexists
    by_cases hF : M.branchObstructionF C branch z = 0
    · exact ⟨{
        point := z
        point_mem := hz
        obstruction_ne := Or.inr (fun hG => hpair ⟨hF, hG⟩)
      }⟩
    · exact ⟨{
        point := z
        point_mem := hz
        obstruction_ne := Or.inl hF
      }⟩

/-- A Maxwell witness rules out the Phase-III obstruction predicate. -/
theorem not_obstructionsVanishOn_of_maxwellWitness
    (M : PositiveQPhaseIIIPatch4 U)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (w : MaxwellBranchObstructionWitness M C branch) :
    ¬M.BranchObstructionsVanishOn C branch := by
  intro hobs
  rcases w.obstruction_ne with hF | hG
  · exact hF (hobs w.point w.point_mem).1
  · exact hG (hobs w.point w.point_mem).2

end PositiveQPhaseIIIPatch4

/-- Evidence-bearing result for one scalar/Maxwell branch. -/
inductive CurvaturePhaseIIIBranchResult
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (branch : RelativeSignScalarBranch4) : Prop where
  | accepted
      (scalar : C.BranchScalarPotentialExists branch)
      (maxwell : M.BranchObstructionsVanishOn C branch)
  | scalarRejected
      (witness : C.ScalarBranchObstructionWitness branch)
  | maxwellRejected
      (scalar : C.BranchScalarPotentialExists branch)
      (witness : M.MaxwellBranchObstructionWitness C branch)

/-- Phase-III accepted branch packaged independently of the classifier's
constructor. -/
structure PhaseIIIAcceptedBranch
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (branch : RelativeSignScalarBranch4) : Prop where
  scalar : C.BranchScalarPotentialExists branch
  maxwell : M.BranchObstructionsVanishOn C branch

/-- Complete two-branch output of the curvature-to-Phase-III classifier. -/
structure CurvaturePhaseIIIBranchPairResult
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U) : Prop where
  plus : CurvaturePhaseIIIBranchResult C M .plus
  minus : CurvaturePhaseIIIBranchResult C M .minus

/-- Noncomputable exact classifier for one branch.  Classical equality of
real curvature tensors is used only to select a constructor; every returned
constructor retains proof evidence for its result. -/
theorem classifyCurvaturePhaseIIIBranch
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    CurvaturePhaseIIIBranchResult C M branch := by
  classical
  by_cases hscalar : C.BranchScalarPotentialExists branch
  · rcases M.obstructionsVanishOn_or_maxwellWitness C branch with
      hmaxwell | hwitness
    · exact .accepted hscalar hmaxwell
    · rcases hwitness with ⟨witness⟩
      exact .maxwellRejected hscalar witness
  · obtain ⟨witness⟩ :=
      C.exists_scalarBranchObstructionWitness_of_not_potential branch
        hconvex hopen hscalar
    exact .scalarRejected witness

/-- The two surviving scalar candidates are tested independently against the
same Phase-III curvature seed; hence zero, one, or two branches may remain. -/
theorem classifyCurvaturePhaseIIIBranches
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    CurvaturePhaseIIIBranchPairResult C M where
  plus := classifyCurvaturePhaseIIIBranch C M .plus hconvex hopen
  minus := classifyCurvaturePhaseIIIBranch C M .minus hconvex hopen

/-- **Concrete curvature-to-Phase-III entry theorem.** The fully reconstructed
amplitude and fixed-probe eigen-one-form fields feed directly into the paired
scalar/Maxwell classifier.  No constituent derivative identity is an input. -/
theorem classifyConcreteFixedProbeCurvaturePhaseIIIBranches
    {U : Set CurvatureCoordinateSpace4}
    (epsilonA epsilonB : ℝ)
    (a b qSq : CurvatureCoordinateSpace4 → ℝ)
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (PA PB : CurvatureCoordinateSpace4 → Matrix4)
    (probeA probeB : CurvatureCoordinateSpace4)
    (M : PositiveQPhaseIIIPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U)
    (hb : ContDiffOn ℝ 1 b U)
    (hqSq : ContDiffOn ℝ 1 qSq U)
    (hg : ContDiffOn ℝ 1 g U)
    (hPA : MatrixFieldContDiffOn 1 U PA)
    (hPB : MatrixFieldContDiffOn 1 U PB)
    (hab : ∀ x ∈ U, a x ≠ b x)
    (hposA : ∀ x ∈ U,
      0 < 2 * epsilonA * reconstructedDiagonalAField a b qSq x)
    (hposB : ∀ x ∈ U,
      0 < 2 * epsilonB * reconstructedDiagonalBField a b qSq x)
    (htime : ∀ x ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector PA probeA)
      (smoothMatrixProjectedVector PA probeA) x < 0)
    (hspace : ∀ x ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector PB probeB)
      (smoothMatrixProjectedVector PB probeB) x) :
    CurvaturePhaseIIIBranchPairResult
      (CurvatureScalarBranchComponentPatch4.ofConcreteFixedProbeCurvatureFields
        epsilonA epsilonB a b qSq g PA PB probeA probeB hopen
        ha hb hqSq hg hPA hPB hab hposA hposB htime hspace) M :=
  classifyCurvaturePhaseIIIBranches
    (CurvatureScalarBranchComponentPatch4.ofConcreteFixedProbeCurvatureFields
      epsilonA epsilonB a b qSq g PA PB probeA probeB hopen
      ha hb hqSq hg hPA hPB hab hposA hposB htime hspace)
    M hconvex hopen

/-- Remaining field-level obligations after a branch has passed the concrete
scalar and Phase-III obstruction tests.  These fields are precisely the data
not implied by first-jet obstruction vanishing: a `C¹` physical Maxwell field,
the Kaluza coupling test, and a compatible normal-gauge `C²` EMD realizer. -/
structure ConditionalUpliftCompletionAt
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  scalarValueAtPoint : ℝ
  scalarRepresentative : CurvatureCoordinateSpace4 → ℝ
  scalarRepresentative_is :
    IsScalarPotentialOn scalarRepresentative
      (C.branchScalarOneForm branch) U
  scalarRepresentative_value :
    scalarRepresentative x = scalarValueAtPoint
  physicalMaxwell : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4
  physicalMaxwellDerivative :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ]
      ContinuousBilinForm CurvatureCoordinateSpace4
  physicalMaxwell_closed :
    IsC1ClosedTwoFormOn physicalMaxwell physicalMaxwellDerivative U
  physicalMaxwell_matches_unweightedSeed :
    ∀ z ∈ U, ∀ i j,
      physicalMaxwell z (coordinateDirection i) (coordinateDirection j) =
        negativeEMDWeight M.coupling scalarRepresentative z *
          (M.exteriorJet z).rotatedF i j
  coupling_is_kaluza : IsKaluzaCoupling M.coupling
  realize :
    (phi : CurvatureCoordinateSpace4 → ℝ) →
      IsScalarPotentialOn phi (C.branchScalarOneForm branch) U →
      phi x = scalarValueAtPoint →
      (A : CurvatureCoordinateSpace4 →
        CurvatureCoordinateSpace4 →L[ℝ] ℝ) →
      IsGaugePotentialOn A physicalMaxwell U →
      LorentzianKaluzaLocalProductGermAt x
  realize_scalar :
    ∀ phi hphi hvalue A hA,
      (realize phi hphi hvalue A hA).fields.phi = phi
  realize_potential :
    ∀ phi hphi hvalue A hA y i,
      (realize phi hphi hvalue A hA).fields.potential y i =
        A y (coordinateDirection i)
  realize_emd :
    ∀ phi hphi hvalue A hA,
      (realize phi hphi hvalue A hA).fields.EMDEquations

namespace ConditionalUpliftCompletionAt

variable {U : Set CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {x : CurvatureCoordinateSpace4}

/-- Turn an accepted curvature/Phase-III branch plus exactly the remaining
field-realization obligations into the established Phase-IV input.  In
particular, `ConditionalUpliftCompletionAt.realize_emd` explicitly assumes the
full `EMDEquations` package for the supplied local product germ. -/
noncomputable def toAcceptedKaluzaBranchAt
    (A : PhaseIIIAcceptedBranch C M branch)
    (K : ConditionalUpliftCompletionAt C M branch x)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    AcceptedKaluzaBranchAt x where
  patch := U
  point_mem := K.point_mem
  patch_convex := hconvex
  scalarOneForm := C.branchScalarOneForm branch
  scalar_closed := by
    cases branch with
    | plus =>
        exact (C.plusField_closed_iff hopen).mpr <|
          (C.plusScalarPotentialExists_iff_curvatureBranchCloses
            hconvex hopen).mp A.scalar
    | minus =>
        exact (C.minusField_closed_iff hopen).mpr <|
          (C.minusScalarPotentialExists_iff_curvatureBranchCloses
            hconvex hopen).mp A.scalar
  scalarValueAtPoint := K.scalarValueAtPoint
  physicalMaxwell := K.physicalMaxwell
  physicalMaxwellDerivative := K.physicalMaxwellDerivative
  physicalMaxwell_closed := K.physicalMaxwell_closed
  coupling := M.coupling
  coupling_is_kaluza := K.coupling_is_kaluza
  realize := K.realize
  realize_scalar := K.realize_scalar
  realize_potential := K.realize_potential
  realize_emd := K.realize_emd

/-- **Curvature-to-Kaluza composition theorem.** Once a branch has passed
the concrete scalar and Phase-III obstruction classifiers, supplying the
remaining realization data--including the full EMD equations through
`ConditionalUpliftCompletionAt.realize_emd`--produces the complete local
Ricci-flat uplift and its full converse/orbit package. -/
theorem exists_completeConditionalKaluzaUplift_of_phaseIIIAccepted
    (A : PhaseIIIAcceptedBranch C M branch)
    (K : ConditionalUpliftCompletionAt C M branch x)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    Nonempty (CompleteConditionalKaluzaUplift
      (K.toAcceptedKaluzaBranchAt A hconvex hopen)) :=
  exists_completeConditionalKaluzaUplift
    (K.toAcceptedKaluzaBranchAt A hconvex hopen)

end ConditionalUpliftCompletionAt

end RainichKaluza
