import RainichKaluza.PhysicalMaxwellFieldRealization

set_option maxSynthPendingDepth 2

/-!
# Realizing the rotated Phase-III rescaled seed

The accepted Phase-III obstruction is written for a duality-rotated seed
`c F0 + s G0`.  This file proves the field-level product rule for that
rotation.  Actual `C¹` realizations of the seed/Hodge-seed pair, together with
actual `C¹` complexion coefficients, canonically produce the
paired rescaled realization consumed by the two-channel field handoff.

The original Maxwell projection remains available, but the Hodge partner is
now retained through positive exponential weighting as a genuine closed
`C¹` field rather than discarded before the normal-gauge seam.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

/-- Full coordinate first jet of the duality rotation `c F0 + s G0`. -/
def rotatedTwoFormFirstJet
    (c s : ℝ) (dc ds : OneForm4)
    (F0 G0 : Matrix4) (dF0 dG0 : Fin 4 → Matrix4) :
    Fin 4 → Matrix4 :=
  fun k => dc k • F0 + c • dF0 k +
    (ds k • G0 + s • dG0 k)

/-- Exteriorizing the full rotation jet gives the four-term exterior product
rule used by `ExteriorDualityJet.rotatedDF`. -/
theorem matrixExteriorDerivative_rotatedTwoFormFirstJet
    (c s : ℝ) (dc ds : OneForm4)
    (F0 G0 : Matrix4) (dF0 dG0 : Fin 4 → Matrix4) :
    matrixExteriorDerivative
        (rotatedTwoFormFirstJet c s dc ds F0 G0 dF0 dG0) =
      matrixOneWedgeTwo dc F0 +
        c • matrixExteriorDerivative dF0 +
        matrixOneWedgeTwo ds G0 +
        s • matrixExteriorDerivative dG0 := by
  ext k i j
  simp [matrixExteriorDerivative, rotatedTwoFormFirstJet,
    matrixOneWedgeTwo, matrixOneWedgeTwoTensor]
  ring

/-- Full coordinate first jet of the rotated Hodge partner
`-s F0 + c G0`. -/
def rotatedHodgeTwoFormFirstJet
    (c s : ℝ) (dc ds : OneForm4)
    (F0 G0 : Matrix4) (dF0 dG0 : Fin 4 → Matrix4) :
    Fin 4 → Matrix4 :=
  rotatedTwoFormFirstJet (-s) c (-ds) dc F0 G0 dF0 dG0

/-- Exteriorizing the rotated-Hodge first jet gives exactly
`ExteriorDualityJet.rotatedDG`. -/
theorem matrixExteriorDerivative_rotatedHodgeTwoFormFirstJet
    (c s : ℝ) (dc ds : OneForm4)
    (F0 G0 : Matrix4) (dF0 dG0 : Fin 4 → Matrix4) :
    matrixExteriorDerivative
        (rotatedHodgeTwoFormFirstJet c s dc ds F0 G0 dF0 dG0) =
      -(matrixOneWedgeTwo ds F0) +
        (-s) • matrixExteriorDerivative dF0 +
        matrixOneWedgeTwo dc G0 +
        c • matrixExteriorDerivative dG0 := by
  rw [rotatedHodgeTwoFormFirstJet,
    matrixExteriorDerivative_rotatedTwoFormFirstJet]
  simp only [map_neg, neg_smul]
  rfl

@[simp]
theorem matrixContinuousBilinForm4_add (F G : Matrix4) :
    matrixContinuousBilinForm4 (F + G) =
      matrixContinuousBilinForm4 F + matrixContinuousBilinForm4 G := by
  change matrixContinuousBilinForm4Linear (F + G) =
    matrixContinuousBilinForm4Linear F +
      matrixContinuousBilinForm4Linear G
  exact map_add matrixContinuousBilinForm4Linear F G

/-- Matrix unit used to reconstruct a two-form field from its sixteen scalar
entry fields without choosing a norm on `Matrix4`. -/
def matrixUnit4 (i j : Fin 4) : Matrix4 :=
  fun a b => if a = i ∧ b = j then 1 else 0

@[simp]
theorem matrixContinuousBilinForm4_matrixUnit4_coordinateDirection
    (i j a b : Fin 4) :
    matrixContinuousBilinForm4 (matrixUnit4 i j)
      (coordinateDirection a) (coordinateDirection b) =
        if a = i ∧ b = j then 1 else 0 := by
  rw [matrixContinuousBilinForm4_coordinateDirection]
  rfl

/-- Every matrix bilinear form is the finite sum of its scalar entries times
the corresponding matrix-unit forms. -/
theorem matrixContinuousBilinForm4_eq_sum_units (F : Matrix4) :
    matrixContinuousBilinForm4 F =
      ∑ i, ∑ j, F i j • matrixContinuousBilinForm4 (matrixUnit4 i j) := by
  have hmatrix : F = ∑ i, ∑ j, F i j • matrixUnit4 i j := by
    apply Matrix.ext
    intro a b
    change F a b = ∑ i, ∑ j, F i j * matrixUnit4 i j a b
    classical
    symm
    calc
      (∑ i, ∑ j, F i j * matrixUnit4 i j a b) =
          ∑ j, F a j * matrixUnit4 a j a b := by
        apply Finset.sum_eq_single a
        · intro i _ hia
          have hai : a ≠ i := Ne.symm hia
          simp [matrixUnit4, hai]
        · simp
      _ = F a b * matrixUnit4 a b a b := by
        apply Finset.sum_eq_single b
        · intro j _ hjb
          have hbj : b ≠ j := Ne.symm hjb
          simp [matrixUnit4, hbj]
        · simp
      _ = F a b := by simp [matrixUnit4]
  change matrixContinuousBilinForm4Linear F =
    ∑ i, ∑ j, F i j • matrixContinuousBilinForm4Linear (matrixUnit4 i j)
  calc
    matrixContinuousBilinForm4Linear F =
        matrixContinuousBilinForm4Linear
          (∑ i, ∑ j, F i j • matrixUnit4 i j) :=
      congrArg matrixContinuousBilinForm4Linear hmatrix
    _ = ∑ i, ∑ j,
        F i j • matrixContinuousBilinForm4Linear (matrixUnit4 i j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]

/-- The corresponding finite sum of scalar entry derivatives is exactly the
canonical continuous-bilinear derivative of the matrix first jet. -/
theorem matrixFirstJetBilinFDeriv_eq_sum_units
    (D : Fin 4 → Matrix4) :
    matrixFirstJetBilinFDeriv D =
      ∑ i, ∑ j,
        (oneForm4ContinuousLinearMap (fun k => D k i j)).smulRight
          (matrixContinuousBilinForm4 (matrixUnit4 i j)) := by
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro k
  simp only [Pi.basisFun_apply]
  rw [← coordinateDirection_eq_single k]
  change matrixContinuousBilinForm4CLM
      (matrixFirstJetCLM D (coordinateDirection k)) =
    (∑ i, ∑ j,
      (oneForm4ContinuousLinearMap (fun d => D d i j)).smulRight
        (matrixContinuousBilinForm4 (matrixUnit4 i j)))
      (coordinateDirection k)
  rw [matrixFirstJetCLM_coordinateDirection,
    matrixContinuousBilinForm4CLM_apply]
  calc
    matrixContinuousBilinForm4 (D k) =
        ∑ i, ∑ j, D k i j •
          matrixContinuousBilinForm4 (matrixUnit4 i j) :=
      matrixContinuousBilinForm4_eq_sum_units (D k)
    _ = (∑ i, ∑ j,
        (oneForm4ContinuousLinearMap
          (fun d : Fin 4 => (D d) i j)).smulRight
            (matrixContinuousBilinForm4 (matrixUnit4 i j)))
        (coordinateDirection k) := by
      rw [sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [ContinuousLinearMap.smulRight_apply,
        oneForm4ContinuousLinearMap_coordinateDirection]

/-- Componentwise scalar Frechet derivatives assemble into the actual
continuous-bilinear derivative of a matrix-valued two-form field. -/
theorem hasFDerivAt_matrixContinuousBilinForm4_of_entries
    (F : BaseCoordinateSpace → Matrix4) (D : Fin 4 → Matrix4)
    (z : BaseCoordinateSpace)
    (hentries : ∀ i j,
      HasFDerivAt (fun y => F y i j)
        (oneForm4ContinuousLinearMap (fun k => D k i j)) z) :
    HasFDerivAt (fun y => matrixContinuousBilinForm4 (F y))
      (matrixFirstJetBilinFDeriv D) z := by
  rw [show (fun y => matrixContinuousBilinForm4 (F y)) =
      fun y => ∑ i, ∑ j,
        F y i j • matrixContinuousBilinForm4 (matrixUnit4 i j) by
    funext y
    exact matrixContinuousBilinForm4_eq_sum_units (F y)]
  rw [matrixFirstJetBilinFDeriv_eq_sum_units]
  apply HasFDerivAt.fun_sum
  intro i _
  apply HasFDerivAt.fun_sum
  intro j _
  exact (hentries i j).smul_const
    (matrixContinuousBilinForm4 (matrixUnit4 i j))

/-- The full rotation jet is the genuine sum of the two scalar product-rule
derivatives after matrix-to-form conversion. -/
theorem matrixFirstJetBilinFDeriv_rotatedTwoFormFirstJet
    (c s : ℝ) (dc ds : OneForm4)
    (F0 G0 : Matrix4) (dF0 dG0 : Fin 4 → Matrix4) :
    matrixFirstJetBilinFDeriv
        (rotatedTwoFormFirstJet c s dc ds F0 G0 dF0 dG0) =
      (c • matrixFirstJetBilinFDeriv dF0 +
        (oneForm4ContinuousLinearMap dc).smulRight
          (matrixContinuousBilinForm4 F0)) +
      (s • matrixFirstJetBilinFDeriv dG0 +
        (oneForm4ContinuousLinearMap ds).smulRight
          (matrixContinuousBilinForm4 G0)) := by
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro k
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro j
  simp only [Pi.basisFun_apply]
  rw [← coordinateDirection_eq_single k,
    ← coordinateDirection_eq_single i,
    ← coordinateDirection_eq_single j]
  change matrixFirstJetBilinFDeriv
      (rotatedTwoFormFirstJet c s dc ds F0 G0 dF0 dG0)
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) =
    ((c • matrixFirstJetBilinFDeriv dF0 +
        (oneForm4ContinuousLinearMap dc).smulRight
          (matrixContinuousBilinForm4 F0)) +
      (s • matrixFirstJetBilinFDeriv dG0 +
        (oneForm4ContinuousLinearMap ds).smulRight
          (matrixContinuousBilinForm4 G0)))
      (coordinateDirection k) (coordinateDirection i)
        (coordinateDirection j)
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply,
    matrixFirstJetBilinFDeriv_coordinateDirection,
    matrixContinuousBilinForm4_coordinateDirection,
    oneForm4ContinuousLinearMap_coordinateDirection,
    rotatedTwoFormFirstJet, Matrix.add_apply, Matrix.smul_apply]
  ring

namespace RescaledMaxwellMatrixC1On

variable {U : Set BaseCoordinateSpace}

/-- Each coordinate component of a genuine matrix `C¹` realization has the
stored component jet as its actual Frechet derivative. -/
theorem hasFDerivAt_field_component
    (S : RescaledMaxwellMatrixC1On U) (z : BaseCoordinateSpace)
    (hz : z ∈ U) (i j : Fin 4) :
    HasFDerivAt (fun y ↦ S.field y i j)
      (oneForm4ContinuousLinearMap (fun k ↦ S.firstJet z k i j)) z := by
  have hi := (S.differentiable z hz).clm_apply
    (hasFDerivAt_const (coordinateDirection i) z)
  have hij := hi.clm_apply
    (hasFDerivAt_const (coordinateDirection j) z)
  have hderiv :
      ((matrixContinuousBilinForm4 (S.field z)) (coordinateDirection i) ∘L 0) +
        ((matrixContinuousBilinForm4 (S.field z) ∘L 0) +
          (matrixFirstJetBilinFDeriv (S.firstJet z)).flip
            (coordinateDirection i)).flip (coordinateDirection j) =
      oneForm4ContinuousLinearMap (fun k ↦ S.firstJet z k i j) := by
    ext u
    simp only [ContinuousLinearMap.comp_apply, zero_apply, add_apply,
      ContinuousLinearMap.flip_apply,
      matrixFirstJetBilinFDeriv_apply,
      oneForm4ContinuousLinearMap_apply, oneForm4Evaluate]
    simp [coordinateDirection, Fin.sum_univ_succ]
    ring
  rw [hderiv] at hij
  simpa only [matrixContinuousBilinForm4_coordinateDirection] using hij

/-- A genuine matrix realization with continuous stored first jet is
entrywise `C¹` on every open patch.  Consequently smooth stress-fibre
theorems can consume the physical field directly; no redundant smoothness
certificate is needed. -/
theorem contDiffOn_field
    (S : RescaledMaxwellMatrixC1On U) (hopen : IsOpen U) :
    MatrixFieldContDiffOn 1 U S.field := by
  intro i j
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      hopen.uniqueDiffOn]
  refine ⟨by simp, fun z ↦ oneForm4ContinuousLinearMap
    (fun k ↦ S.firstJet z k i j), ?_, ?_⟩
  · rw [contDiffOn_zero]
    apply continuousOn_clm_apply.mpr
    intro y
    change ContinuousOn
      (fun z ↦ ∑ k, S.firstJet z k i j * y k) U
    apply continuousOn_finsetSum Finset.univ
    intro k _
    exact (S.firstJet_continuous k i j).mul continuousOn_const
  · intro z hz
    exact (S.hasFDerivAt_field_component z hz i j).hasFDerivWithinAt

/-- Every coordinate component of a realized matrix two-form is continuous.
The proof uses the actual Frechet derivative after matrix-to-form conversion. -/
theorem continuousOn_field_component
    (S : RescaledMaxwellMatrixC1On U) (i j : Fin 4) :
    ContinuousOn (fun z => S.field z i j) U := by
  have hfield : ContinuousOn
      (fun z => matrixContinuousBilinForm4 (S.field z)) U :=
    fun z hz => ((S.differentiable z hz).continuousAt).continuousWithinAt
  simpa only [matrixContinuousBilinForm4_coordinateDirection] using
    (continuousOn_clm_apply.mp
      (continuousOn_clm_apply.mp hfield (coordinateDirection i))
      (coordinateDirection j))

end RescaledMaxwellMatrixC1On

namespace PositiveQPhaseIIIPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- Full displayed first jet of the transported positive-`q` seed. -/
noncomputable def seedFirstJet
    (M : PositiveQPhaseIIIPatch4 U)
    (z : CurvatureCoordinateSpace4) : Fin 4 → Matrix4 :=
  localPositiveQSeedFirstDerivative (M.L z) (M.dL z)
    (M.q z) (M.dq z)

/-- Full displayed first jet of the transported Hodge seed. -/
noncomputable def hodgeSeedFirstJet
    (M : PositiveQPhaseIIIPatch4 U)
    (z : CurvatureCoordinateSpace4) : Fin 4 → Matrix4 :=
  localPositiveQHodgeSeedFirstDerivative (M.L z) (M.dL z)
    (M.q z) (M.dq z)

end PositiveQPhaseIIIPatch4

/-- Canonical positive-`q` Hodge seed as a varying matrix. -/
noncomputable def smoothCanonicalPositiveQHodgeSeed
    {X : Type*} (q : X → ℝ) (z : X) : Matrix4 :=
  canonicalHodgeStar (Real.sqrt (2 * q z)) 0

/-- The canonical Hodge seed has the same smooth amplitude regularity as the
electric seed. -/
theorem contDiffOn_smoothCanonicalPositiveQHodgeSeed
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {q : X → ℝ}
    (hqSmooth : ContDiffOn ℝ n q U) (hq : ∀ z ∈ U, 0 < q z) :
    MatrixFieldContDiffOn n U (smoothCanonicalPositiveQHodgeSeed q) := by
  have harg : ContDiffOn ℝ n (fun z => 2 * q z) U :=
    contDiffOn_const.mul hqSmooth
  have hamp : ContDiffOn ℝ n (fun z => Real.sqrt (2 * q z)) U :=
    harg.sqrt (fun z hz => by linarith [hq z hz])
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [smoothCanonicalPositiveQHodgeSeed, canonicalHodgeStar,
      canonicalMaxwellTwoForm] <;>
    first | exact contDiffOn_const | exact hamp | exact hamp.neg

/-- A smooth frame and positive smooth magnitude produce a smooth transported
Hodge seed. -/
theorem contDiffOn_transportedPositiveQHodgeSeed
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X}
    {L : X → Matrix4} {q : X → ℝ}
    (hL : MatrixFieldContDiffOn n U L)
    (hqSmooth : ContDiffOn ℝ n q U) (hq : ∀ z ∈ U, 0 < q z) :
    MatrixFieldContDiffOn n U
      (fun z => transportedPositiveQHodgeSeed (L z) (q z)) := by
  have hG := contDiffOn_smoothCanonicalPositiveQHodgeSeed hqSmooth hq
  change MatrixFieldContDiffOn n U
    (fun z => (L z)ᵀ * smoothCanonicalPositiveQHodgeSeed q z * L z)
  exact (hL.transpose.mul hG).mul hL

/-- Entrywise `C¹` regularity plus equality of the four coordinate derivative
components gives the exact scalar Frechet derivative used by the matrix-field
assembler. -/
theorem hasFDerivAt_matrixEntry_of_coordinateFDeriv
    {U : Set CurvatureCoordinateSpace4}
    (F : CurvatureCoordinateSpace4 → Matrix4)
    (D : CurvatureCoordinateSpace4 → Fin 4 → Matrix4)
    (hopen : IsOpen U) (hF : MatrixFieldContDiffOn 1 U F)
    (hD : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => F y i j) z =
        fun k => D z k i j)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) (i j : Fin 4) :
    HasFDerivAt (fun y => F y i j)
      (oneForm4ContinuousLinearMap (fun k => D z k i j)) z := by
  have hdiffAt : DifferentiableAt ℝ (fun y => F y i j) z :=
    ((hF i j).differentiableOn_one z hz).differentiableAt
      (hopen.mem_nhds hz)
  apply hdiffAt.hasFDerivAt.congr_fderiv
  ext u
  rw [scalarField_fderiv_eq_coordinateEvaluation]
  rw [hD z hz i j]
  rfl

/-- Actual `C¹` realizations of the transported positive-`q` seed and its
Hodge partner, plus actual `C¹` complexion coefficients.  Their values and
exteriorized first jets match the Phase-III `ExteriorDualityJet`. -/
structure PositiveQPhaseIIISeedPairC1Realization
    {U : Set CurvatureCoordinateSpace4}
    (M : PositiveQPhaseIIIPatch4 U) where
  seed : RescaledMaxwellMatrixC1On U
  hodgeSeed : RescaledMaxwellMatrixC1On U
  seed_field_eq : ∀ z ∈ U,
    seed.field z = (M.exteriorJet z).F0
  hodgeSeed_field_eq : ∀ z ∈ U,
    hodgeSeed.field z = (M.exteriorJet z).G0
  seed_exteriorFirstJet_eq : ∀ z ∈ U,
    matrixExteriorDerivative (seed.firstJet z) =
      (M.exteriorJet z).dF0
  hodgeSeed_exteriorFirstJet_eq : ∀ z ∈ U,
    matrixExteriorDerivative (hodgeSeed.firstJet z) =
      (M.exteriorJet z).dG0
  c_fderiv : ∀ z ∈ U,
    HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z
  s_fderiv : ∀ z ∈ U,
    HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z
  dc_continuous : ContinuousOn M.dc U
  ds_continuous : ContinuousOn M.ds U

namespace PositiveQPhaseIIISeedPairC1Realization

variable {U : Set CurvatureCoordinateSpace4}
  {M : PositiveQPhaseIIIPatch4 U}

/-- Build the constituent seed-pair realization from scalar coordinate-entry
Frechet derivatives.  The finite matrix-to-bilinear reconstruction theorem
then supplies derivatives in arbitrary directions. -/
noncomputable def ofCoordinateFDerivs
    (M : PositiveQPhaseIIIPatch4 U)
    (hseed : ∀ z ∈ U, ∀ i j,
      HasFDerivAt (fun y => (M.exteriorJet y).F0 i j)
        (oneForm4ContinuousLinearMap
          (fun k => M.seedFirstJet z k i j)) z)
    (hhodgeSeed : ∀ z ∈ U, ∀ i j,
      HasFDerivAt (fun y => (M.exteriorJet y).G0 i j)
        (oneForm4ContinuousLinearMap
          (fun k => M.hodgeSeedFirstJet z k i j)) z)
    (hseedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.seedFirstJet z k i j) U)
    (hhodgeSeedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.hodgeSeedFirstJet z k i j) U)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PositiveQPhaseIIISeedPairC1Realization M where
  seed := {
    field := fun z => (M.exteriorJet z).F0
    firstJet := M.seedFirstJet
    differentiable := by
      intro z hz
      exact hasFDerivAt_matrixContinuousBilinForm4_of_entries
        (fun y => (M.exteriorJet y).F0) (M.seedFirstJet z) z
        (hseed z hz)
    firstJet_continuous := hseedJetContinuous
    alternating := by
      intro z _
      change (transportTwoForm (M.L z)
        (canonicalMaxwellTwoForm (Real.sqrt (2 * M.q z)) 0))ᵀ =
        -transportTwoForm (M.L z)
          (canonicalMaxwellTwoForm (Real.sqrt (2 * M.q z)) 0)
      exact transported_seed_transpose (M.L z) (M.q z)
  }
  hodgeSeed := {
    field := fun z => (M.exteriorJet z).G0
    firstJet := M.hodgeSeedFirstJet
    differentiable := by
      intro z hz
      exact hasFDerivAt_matrixContinuousBilinForm4_of_entries
        (fun y => (M.exteriorJet y).G0) (M.hodgeSeedFirstJet z) z
        (hhodgeSeed z hz)
    firstJet_continuous := hhodgeSeedJetContinuous
    alternating := by
      intro z _
      change (transportTwoForm (M.L z)
        (canonicalHodgeStar (Real.sqrt (2 * M.q z)) 0))ᵀ =
        -transportTwoForm (M.L z)
          (canonicalHodgeStar (Real.sqrt (2 * M.q z)) 0)
      apply transportTwoForm_transpose
      exact canonicalMaxwellTwoForm_transpose _ _
  }
  seed_field_eq := by intros; rfl
  hodgeSeed_field_eq := by intros; rfl
  seed_exteriorFirstJet_eq := by intros; rfl
  hodgeSeed_exteriorFirstJet_eq := by intros; rfl
  c_fderiv := hc
  s_fderiv := hs
  dc_continuous := hdc
  ds_continuous := hds

/-- Smooth `L,q` data reduce seed realization to the two explicit coordinate
first-jet identities.  Once those identities and jet continuity are supplied,
the actual seed/Hodge-seed Frechet derivatives are reconstructed
automatically. -/
noncomputable def ofSmoothCoordinateJets
    (M : PositiveQPhaseIIIPatch4 U)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 1 U M.L)
    (hq : ContDiffOn ℝ 1 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hseedJet : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv
          (fun y => (M.exteriorJet y).F0 i j) z =
        fun k => M.seedFirstJet z k i j)
    (hhodgeSeedJet : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv
          (fun y => (M.exteriorJet y).G0 i j) z =
        fun k => M.hodgeSeedFirstJet z k i j)
    (hseedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.seedFirstJet z k i j) U)
    (hhodgeSeedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.hodgeSeedFirstJet z k i j) U)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PositiveQPhaseIIISeedPairC1Realization M := by
  have hseedSmooth : MatrixFieldContDiffOn 1 U
      (fun z => (M.exteriorJet z).F0) := by
    change MatrixFieldContDiffOn 1 U
      (smoothTransportedPositiveQSeed M.L M.q)
    exact contDiffOn_smoothTransportedPositiveQSeed hL hq hqPos
  have hhodgeSmooth : MatrixFieldContDiffOn 1 U
      (fun z => (M.exteriorJet z).G0) := by
    simpa only [PositiveQPhaseIIIPatch4.exteriorJet,
      localPositiveQExteriorDualityJet] using
      (contDiffOn_transportedPositiveQHodgeSeed hL hq hqPos)
  exact ofCoordinateFDerivs M
    (fun z hz i j =>
      hasFDerivAt_matrixEntry_of_coordinateFDeriv
        (fun y => (M.exteriorJet y).F0) M.seedFirstJet
        hopen hseedSmooth hseedJet z hz i j)
    (fun z hz i j =>
      hasFDerivAt_matrixEntry_of_coordinateFDeriv
        (fun y => (M.exteriorJet y).G0) M.hodgeSeedFirstJet
        hopen hhodgeSmooth hhodgeSeedJet z hz i j)
    hseedJetContinuous hhodgeSeedJetContinuous hc hs hdc hds

/-- Actual full first jet of the rotated rescaled field. -/
def rotatedFirstJet
    (S : PositiveQPhaseIIISeedPairC1Realization M)
    (z : CurvatureCoordinateSpace4) : Fin 4 → Matrix4 :=
  rotatedTwoFormFirstJet (M.c z) (M.s z) (M.dc z) (M.ds z)
    (S.seed.field z) (S.hodgeSeed.field z)
    (S.seed.firstJet z) (S.hodgeSeed.firstJet z)

/-- The two constituent `C¹` fields and complexion product rule assemble an
actual `C¹` rescaled Maxwell field. -/
noncomputable def rotatedC1
    (S : PositiveQPhaseIIISeedPairC1Realization M) :
    RescaledMaxwellMatrixC1On U where
  field := fun z => M.c z • S.seed.field z +
    M.s z • S.hodgeSeed.field z
  firstJet := S.rotatedFirstJet
  differentiable := by
    intro z hz
    have hc := (S.c_fderiv z hz).smul (S.seed.differentiable z hz)
    have hs := (S.s_fderiv z hz).smul
      (S.hodgeSeed.differentiable z hz)
    have hsum := hc.add hs
    rw [show (fun y => matrixContinuousBilinForm4
        (M.c y • S.seed.field y + M.s y • S.hodgeSeed.field y)) =
      (M.c • fun y => matrixContinuousBilinForm4 (S.seed.field y)) +
        (M.s • fun y =>
          matrixContinuousBilinForm4 (S.hodgeSeed.field y)) by
      funext y
      change matrixContinuousBilinForm4
          (M.c y • S.seed.field y + M.s y • S.hodgeSeed.field y) =
        M.c y • matrixContinuousBilinForm4 (S.seed.field y) +
          M.s y • matrixContinuousBilinForm4 (S.hodgeSeed.field y)
      rw [matrixContinuousBilinForm4_add,
        matrixContinuousBilinForm4_smul,
        matrixContinuousBilinForm4_smul]]
    change HasFDerivAt
      ((M.c • fun y => matrixContinuousBilinForm4 (S.seed.field y)) +
        (M.s • fun y => matrixContinuousBilinForm4
          (S.hodgeSeed.field y)))
      (matrixFirstJetBilinFDeriv
        (rotatedTwoFormFirstJet (M.c z) (M.s z) (M.dc z) (M.ds z)
          (S.seed.field z) (S.hodgeSeed.field z)
          (S.seed.firstJet z) (S.hodgeSeed.firstJet z))) z
    rw [matrixFirstJetBilinFDeriv_rotatedTwoFormFirstJet]
    exact hsum
  firstJet_continuous := by
    intro k i j
    have hc : ContinuousOn M.c U :=
      fun z hz => ((S.c_fderiv z hz).continuousAt).continuousWithinAt
    have hs : ContinuousOn M.s U :=
      fun z hz => ((S.s_fderiv z hz).continuousAt).continuousWithinAt
    have hdc := continuousOn_pi.mp S.dc_continuous k
    have hds := continuousOn_pi.mp S.ds_continuous k
    change ContinuousOn (fun z =>
      M.dc z k * S.seed.field z i j +
          M.c z * S.seed.firstJet z k i j +
        (M.ds z k * S.hodgeSeed.field z i j +
          M.s z * S.hodgeSeed.firstJet z k i j)) U
    exact ((hdc.mul (S.seed.continuousOn_field_component i j)).add
      (hc.mul (S.seed.firstJet_continuous k i j))).add
        ((hds.mul (S.hodgeSeed.continuousOn_field_component i j)).add
          (hs.mul (S.hodgeSeed.firstJet_continuous k i j)))
  alternating := by
    intro z hz
    rw [Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_smul, S.seed.alternating z hz,
      S.hodgeSeed.alternating z hz]
    simp only [smul_neg, neg_add_rev]
    abel

/-- Actual full first jet of the rotated rescaled Hodge partner. -/
def rotatedHodgeFirstJet
    (S : PositiveQPhaseIIISeedPairC1Realization M)
    (z : CurvatureCoordinateSpace4) : Fin 4 → Matrix4 :=
  rotatedHodgeTwoFormFirstJet (M.c z) (M.s z) (M.dc z) (M.ds z)
    (S.seed.field z) (S.hodgeSeed.field z)
    (S.seed.firstJet z) (S.hodgeSeed.firstJet z)

/-- The same constituent seed pair and complexion product rule assemble an
actual `C¹` realization of the rotated Hodge channel. -/
noncomputable def rotatedHodgeC1
    (S : PositiveQPhaseIIISeedPairC1Realization M) :
    RescaledMaxwellMatrixC1On U where
  field := fun z => (-M.s z) • S.seed.field z +
    M.c z • S.hodgeSeed.field z
  firstJet := S.rotatedHodgeFirstJet
  differentiable := by
    intro z hz
    have hs := (S.s_fderiv z hz).neg.smul (S.seed.differentiable z hz)
    have hc := (S.c_fderiv z hz).smul
      (S.hodgeSeed.differentiable z hz)
    have hsum := hs.add hc
    rw [show (fun y => matrixContinuousBilinForm4
        ((-M.s y) • S.seed.field y + M.c y • S.hodgeSeed.field y)) =
      ((-M.s) • (fun y => matrixContinuousBilinForm4 (S.seed.field y))) +
        (M.c • fun y =>
          matrixContinuousBilinForm4 (S.hodgeSeed.field y)) by
      funext y
      change matrixContinuousBilinForm4
          ((-M.s y) • S.seed.field y + M.c y • S.hodgeSeed.field y) =
        (-M.s y) • matrixContinuousBilinForm4 (S.seed.field y) +
          M.c y • matrixContinuousBilinForm4 (S.hodgeSeed.field y)
      rw [matrixContinuousBilinForm4_add,
        matrixContinuousBilinForm4_smul,
        matrixContinuousBilinForm4_smul]]
    change HasFDerivAt
      ((-M.s) • (fun y => matrixContinuousBilinForm4 (S.seed.field y)) +
        M.c • fun y => matrixContinuousBilinForm4
          (S.hodgeSeed.field y))
      (matrixFirstJetBilinFDeriv
        (rotatedHodgeTwoFormFirstJet
          (M.c z) (M.s z) (M.dc z) (M.ds z)
          (S.seed.field z) (S.hodgeSeed.field z)
          (S.seed.firstJet z) (S.hodgeSeed.firstJet z))) z
    rw [rotatedHodgeTwoFormFirstJet,
      matrixFirstJetBilinFDeriv_rotatedTwoFormFirstJet]
    have hneg : oneForm4ContinuousLinearMap (-M.ds z) =
        -oneForm4ContinuousLinearMap (M.ds z) := by
      ext u
      simp [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate]
    rw [hneg]
    exact hsum
  firstJet_continuous := by
    intro k i j
    have hc : ContinuousOn M.c U :=
      fun z hz => ((S.c_fderiv z hz).continuousAt).continuousWithinAt
    have hs : ContinuousOn M.s U :=
      fun z hz => ((S.s_fderiv z hz).continuousAt).continuousWithinAt
    have hdc := continuousOn_pi.mp S.dc_continuous k
    have hds := continuousOn_pi.mp S.ds_continuous k
    change ContinuousOn (fun z =>
      -(M.ds z k) * S.seed.field z i j +
          (-M.s z) * S.seed.firstJet z k i j +
        (M.dc z k * S.hodgeSeed.field z i j +
          M.c z * S.hodgeSeed.firstJet z k i j)) U
    exact (((hds.neg.mul (S.seed.continuousOn_field_component i j)).add
      (hs.neg.mul (S.seed.firstJet_continuous k i j))).add
        ((hdc.mul (S.hodgeSeed.continuousOn_field_component i j)).add
          (hc.mul (S.hodgeSeed.firstJet_continuous k i j))))
  alternating := by
    intro z hz
    rw [Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_smul, S.seed.alternating z hz,
      S.hodgeSeed.alternating z hz]
    simp only [smul_neg, neg_add_rev]
    abel

/-- **Seed-pair realization theorem.** Constituent `C¹` seed realizations and
actual complexion derivatives construct the precise rescaled realization
required by the accepted-jet-to-physical-field theorem. -/
noncomputable def toRescaledMaxwellC1Realization
    (S : PositiveQPhaseIIISeedPairC1Realization M) :
    PositiveQPhaseIIIRescaledMaxwellC1Realization M where
  c1 := S.rotatedC1
  field_eq := by
    intro z hz
    change M.c z • S.seed.field z + M.s z • S.hodgeSeed.field z =
      (M.exteriorJet z).rotatedF
    rw [S.seed_field_eq z hz, S.hodgeSeed_field_eq z hz]
    rfl
  exteriorFirstJet_eq := by
    intro z hz
    change matrixExteriorDerivative
      (rotatedTwoFormFirstJet (M.c z) (M.s z) (M.dc z) (M.ds z)
        (S.seed.field z) (S.hodgeSeed.field z)
        (S.seed.firstJet z) (S.hodgeSeed.firstJet z)) =
      (M.exteriorJet z).rotatedDF matrixOneWedgeTwo
    rw [matrixExteriorDerivative_rotatedTwoFormFirstJet,
      S.seed_field_eq z hz, S.hodgeSeed_field_eq z hz,
      S.seed_exteriorFirstJet_eq z hz,
      S.hodgeSeed_exteriorFirstJet_eq z hz]
    rfl

/-- **Paired seed-realization theorem.** The actual seed pair produces both
rescaled `C¹` channels tested by Phase III, not only the Maxwell channel. -/
noncomputable def toRescaledMaxwellC1PairRealization
    (S : PositiveQPhaseIIISeedPairC1Realization M) :
    PositiveQPhaseIIIRescaledMaxwellC1PairRealization M where
  maxwell := S.toRescaledMaxwellC1Realization
  hodge := S.rotatedHodgeC1
  hodge_field_eq := by
    intro z hz
    change (-M.s z) • S.seed.field z + M.c z • S.hodgeSeed.field z =
      (M.exteriorJet z).rotatedG
    rw [S.seed_field_eq z hz, S.hodgeSeed_field_eq z hz]
    rfl
  hodge_exteriorFirstJet_eq := by
    intro z hz
    change matrixExteriorDerivative
      (rotatedHodgeTwoFormFirstJet
        (M.c z) (M.s z) (M.dc z) (M.ds z)
        (S.seed.field z) (S.hodgeSeed.field z)
        (S.seed.firstJet z) (S.hodgeSeed.firstJet z)) =
      (M.exteriorJet z).rotatedDG matrixOneWedgeTwo
    rw [matrixExteriorDerivative_rotatedHodgeTwoFormFirstJet,
      S.seed_field_eq z hz, S.hodgeSeed_field_eq z hz,
      S.seed_exteriorFirstJet_eq z hz,
      S.hodgeSeed_exteriorFirstJet_eq z hz]
    rfl

end PositiveQPhaseIIISeedPairC1Realization

namespace PhaseIIIAcceptedBranch

variable {U : Set CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- **Paired Phase-III field handoff.** An accepted curvature branch and an
actual realization of both rotated seed channels canonically produce the
closed physical Maxwell field and the closed positively weighted Hodge flux.
Thus neither exterior EMD equation needs to be re-assumed by the downstream
normal-gauge completion. -/
noncomputable def toPhysicalMaxwellC1PairRealization
    (A : PhaseIIIAcceptedBranch C M branch)
    (R : PositiveQPhaseIIIRescaledMaxwellC1PairRealization M)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U) :
    PhaseIIIPhysicalMaxwellC1PairRealization C M branch := by
  let P := A.toPhysicalMaxwellC1Realization R.maxwell hopen hstar
  have hphiCoordinate : ∀ z ∈ U,
      HasFDerivAt P.scalarRepresentative
        (oneForm4ContinuousLinearMap
          (C.branchScalarOneFormValue branch z)) z := by
    intro z hz
    rw [← C.branchScalarOneForm_eq_coordinateValue branch z]
    exact P.scalarRepresentative_is z hz
  have hclosures :=
    M.branchObstructionsVanishOn_gives_closed_exponentialWeightJets
      C branch A.maxwell
        (negativeEMDWeight M.coupling P.scalarRepresentative)
        (positiveEMDWeight M.coupling P.scalarRepresentative)
  have hfluxClosure : ∀ z ∈ U,
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo
        (positiveEMDWeight M.coupling P.scalarRepresentative z)
        (positiveEMDWeightDerivative M.coupling
          (positiveEMDWeight M.coupling P.scalarRepresentative z)
          (C.branchScalarOneFormValue branch z))
        (R.hodge.field z)
        (matrixExteriorDerivative (R.hodge.firstJet z)) = 0 := by
    intro z hz
    rw [R.hodge_field_eq z hz, R.hodge_exteriorFirstJet_eq z hz]
    exact (hclosures z hz).2
  exact {
    maxwell := P
    weightedHodgeFlux :=
      R.hodge.weightedDualField M.coupling P.scalarRepresentative
    weightedHodgeFluxDerivative :=
      R.hodge.weightedDualFDeriv M.coupling P.scalarRepresentative
        (C.branchScalarOneFormValue branch)
    weightedHodgeFlux_closed :=
      R.hodge.weightedDualField_isC1ClosedTwoFormOn
        M.coupling P.scalarRepresentative
        (C.branchScalarOneFormValue branch) hopen hstar
        hphiCoordinate (C.continuousOn_branchScalarOneFormValue branch)
        hfluxClosure
    weightedHodgeFlux_matches_seed := by
      intro z hz i j
      simp only [RescaledMaxwellMatrixC1On.weightedDualField,
        RescaledMaxwellMatrixC1On.weightedDualMatrix,
        matrixContinuousBilinForm4_coordinateDirection,
        Matrix.smul_apply, smul_eq_mul]
      rw [R.hodge_field_eq z hz]
  }

end PhaseIIIAcceptedBranch

end RainichKaluza
