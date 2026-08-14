import RainichKaluza.GeometricCouplingDetector
import RainichKaluza.PhaseIIITransportedSeedCalculus
import RainichKaluza.CurvatureScalarContribution
import RainichKaluza.CoordinateRicci
import RainichKaluza.AlgebraicEntrance
import RainichKaluza.MetricHodge

/-!
# Fourth-order curvature-seed coupling detector

This file removes the last independently supplied differential datum from the
channel-level detector.  Given fields `L`, `q`, and a curvature-reconstructed
scalar covector `v`, it constructs

* the coordinate jets `dL` and `dq` by actual Frechet differentiation;
* the transported seed exterior channels;
* the effective cosine component `A` from one finite nonzero component;
* `dA` by actual Frechet differentiation of that constructed scalar field;
* the finite fourth-order candidate set and its squared-coupling values.

No Maxwell field, complexion, coupling, or EMD equation is an input.  The
patch-level confluence theorem proves that even source components defining
different local formulas for `A` have the same derivative whenever both
complete-channel candidates are accepted on an open neighborhood.
-/

namespace RainichKaluza

open scoped Matrix Topology

open Set

/-- Actual coordinate derivative of a four-by-four matrix field, taken
entrywise in the four coordinate directions. -/
noncomputable def matrixFieldCoordinateFDeriv4
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4) : Fin 4 → Matrix4 :=
  fun k i j => scalarFieldCoordinateFDeriv (fun y => L y i j) z k

/-- Complete principal-frame channel pair built from actual derivatives of a
transported positive-`q` curvature seed.  The inverse principal frame is the
matrix nonsingular inverse, so it is constructed rather than supplied. -/
noncomputable def curvatureSeedCanonicalChannelField
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) :
    ThreeTensor4 × ThreeTensor4 :=
  transportedPositiveQCanonicalSeedChannels (L z) (L z)⁻¹
    (matrixFieldCoordinateFDeriv4 L z) (q z)
    (scalarFieldCoordinateFDeriv q z)

/-- Scalar field obtained from one of the four explicit complete-channel
cosine quotients.  Its unused channel components remain compatibility
obstructions in the acceptance predicate below. -/
noncomputable def curvatureSeedCosineField
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (source : Fin 4) (z : CurvatureCoordinateSpace4) : ℝ :=
  canonicalCosineCandidateFromChannels (Real.sqrt (2 * q z))
    (pullCovectorToPrincipalFrame (L z)⁻¹ (v z))
    (curvatureSeedCanonicalChannelField L q z) source

/-- The fourth-order covector `dA`, constructed as the actual coordinate
Frechet derivative of the curvature-seed cosine field. -/
noncomputable def curvatureSeedCosineCoordinateDerivative
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (source : Fin 4) (z : CurvatureCoordinateSpace4) : OneForm4 :=
  scalarFieldCoordinateFDeriv
    (curvatureSeedCosineField L q v source) z

/-- Matter-free fourth-order acceptance predicate at a point.  Every input is
either a transported curvature-seed field, its actual derivative, or the
selected curvature scalar covector. -/
def IsCurvatureSeedFourthOrderCandidateAt
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : Prop :=
  IsTransportedSeedFourthOrderCandidate (L z) (L z)⁻¹
    (matrixFieldCoordinateFDeriv4 L z) (q z)
    (scalarFieldCoordinateFDeriv q z) (v z)
    (curvatureSeedCosineCoordinateDerivative L q v choice.1 z)
    choice

/-- Finite accepted choice set of the matter-free fourth-order detector at a
point. -/
noncomputable def acceptedCurvatureSeedFourthOrderChoicesAt
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) :
    Finset FourthOrderComponentChoice := by
  classical
  exact Finset.univ.filter
    (IsCurvatureSeedFourthOrderCandidateAt L q v z)

/-- Squared coupling attached to one matter-free fourth-order choice. -/
noncomputable def curvatureSeedFourthOrderCouplingSqCandidateAt
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  transportedSeedFourthOrderCouplingSqCandidate (L z) (L z)⁻¹
    (matrixFieldCoordinateFDeriv4 L z) (q z)
    (scalarFieldCoordinateFDeriv q z) (v z)
    (curvatureSeedCosineCoordinateDerivative L q v choice.1 z)
    choice

/-- Membership in the constructed finite set is exactly pointwise
fourth-order acceptance. -/
theorem mem_acceptedCurvatureSeedFourthOrderChoicesAt_iff
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) :
    choice ∈ acceptedCurvatureSeedFourthOrderChoicesAt L q v z ↔
      IsCurvatureSeedFourthOrderCandidateAt L q v z choice := by
  classical
  simp [acceptedCurvatureSeedFourthOrderChoicesAt]

/-- If two source formulas agree on a neighborhood, their constructed actual
coordinate derivatives agree at its center. -/
theorem curvatureSeedCosineCoordinateDerivative_eq_of_eventuallyEq
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (source source' : Fin 4) (z : CurvatureCoordinateSpace4)
    (hA : curvatureSeedCosineField L q v source =ᶠ[nhds z]
      curvatureSeedCosineField L q v source') :
    curvatureSeedCosineCoordinateDerivative L q v source z =
      curvatureSeedCosineCoordinateDerivative L q v source' z := by
  unfold curvatureSeedCosineCoordinateDerivative
    scalarFieldCoordinateFDeriv
  rw [Filter.EventuallyEq.fderiv_eq hA]

/-- **Physical quotient-germ derivative bridge.**  If the complete
curvature-seed channels agree on a neighborhood with a physical canonical
channel of cosine component `A`, and one fixed pulled scalar component stays
nonzero there, then the detector's literal quotient field is eventually `A`.
Consequently its actual Frechet derivative is exactly the derivative of that
physical double-angle field.  This is the non-circular calculus seam needed
by actual-metric nonemptiness: it assumes channel equality, not detector
acceptance. -/
theorem curvatureSeedCosineField_eventuallyEq_and_coordinateDerivative_eq_of_physicalGerm
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (eta : CurvatureCoordinateSpace4 → OneForm4)
    (A : CurvatureCoordinateSpace4 → ℝ)
    (source : Fin 4) (z : CurvatureCoordinateSpace4)
    (hq : ∀ᶠ y in nhds z, 0 < q y)
    (hsource : ∀ᶠ y in nhds z,
      pullCovectorToPrincipalFrame (L y)⁻¹ (v y) source ≠ 0)
    (hchannels : ∀ᶠ y in nhds z,
      curvatureSeedCanonicalChannelField L q y =
        canonicalComplexionCouplingChannels (Real.sqrt (2 * q y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (v y))
          (eta y) (A y)) :
    curvatureSeedCosineField L q v source =ᶠ[nhds z] A ∧
      curvatureSeedCosineCoordinateDerivative L q v source z =
        scalarFieldCoordinateFDeriv A z := by
  have hfield : curvatureSeedCosineField L q v source =ᶠ[nhds z] A := by
    filter_upwards [hq, hsource, hchannels] with y hqy hvy hXy
    unfold curvatureSeedCosineField
    exact canonicalCosineCandidateFromChannels_eq
      (Real.sqrt (2 * q y))
      (Real.sqrt_ne_zero'.mpr (by positivity))
      (pullCovectorToPrincipalFrame (L y)⁻¹ (v y))
      (eta y) (A y) (curvatureSeedCanonicalChannelField L q y)
      hXy source hvy
  refine ⟨hfield, ?_⟩
  unfold curvatureSeedCosineCoordinateDerivative
    scalarFieldCoordinateFDeriv
  rw [Filter.EventuallyEq.fderiv_eq hfield]

/-- The derivative in the preceding germ bridge is the displayed
double-angle product rule for any differentiable unit-circle coordinate
fields. -/
theorem scalarFieldCoordinateFDeriv_doubleAngleCosine
    (a : ℝ) (c s : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z) :
    scalarFieldCoordinateFDeriv
        (fun y => a * (c y ^ 2 - s y ^ 2)) z =
      doubleAngleCosineFirstDerivative a (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) := by
  funext k
  unfold scalarFieldCoordinateFDeriv doubleAngleCosineFirstDerivative
  simp only [pow_two]
  change (fderiv ℝ (fun y => a * ((c * c - s * s) y)) z)
      (curvatureCoordinateDirection k) = _
  rw [fderiv_const_mul ((hc.mul hc).sub (hs.mul hs)) a,
    fderiv_sub (hc.mul hc) (hs.mul hs),
    fderiv_mul hc hc, fderiv_mul hs hs]
  simp
  ring

/-- **End-to-end quotient derivative from a physical channel germ.**  Once
the local channel identity is supplied, no acceptance or quotient
differentiation hypothesis remains: the detector's actual `dA` is forced to
be the physical double-angle product-rule covector. -/
theorem curvatureSeedCosineCoordinateDerivative_eq_doubleAngleCosine_of_physicalGerm
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (eta : CurvatureCoordinateSpace4 → OneForm4)
    (a : ℝ) (c s : CurvatureCoordinateSpace4 → ℝ)
    (source : Fin 4) (z : CurvatureCoordinateSpace4)
    (hq : ∀ᶠ y in nhds z, 0 < q y)
    (hsource : ∀ᶠ y in nhds z,
      pullCovectorToPrincipalFrame (L y)⁻¹ (v y) source ≠ 0)
    (hchannels : ∀ᶠ y in nhds z,
      curvatureSeedCanonicalChannelField L q y =
        canonicalComplexionCouplingChannels (Real.sqrt (2 * q y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (v y))
          (eta y) (a * (c y ^ 2 - s y ^ 2)))
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z) :
    curvatureSeedCosineCoordinateDerivative L q v source z =
      doubleAngleCosineFirstDerivative a (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) := by
  rw [(curvatureSeedCosineField_eventuallyEq_and_coordinateDerivative_eq_of_physicalGerm
    L q v eta (fun y => a * (c y ^ 2 - s y ^ 2)) source z
    hq hsource hchannels).2]
  exact scalarFieldCoordinateFDeriv_doubleAngleCosine a c s z hc hs

/-- **Physical-channel predicate from a neighborhood seed-channel identity.**
This is the final calculus composition before the actual geometric splice.
Once the genuine physical EMD field has supplied the canonical seed-channel
identity on a neighborhood of the selected coframe, the detector's literal
quotient derivative and the complete next-order physical predicate follow
without any acceptance hypothesis. -/
theorem isPhysicalConstantCouplingChannel_of_physicalSeedChannelGerm
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v omega : CurvatureCoordinateSpace4 → OneForm4)
    (a : ℝ) (c s : CurvatureCoordinateSpace4 → ℝ)
    (source : Fin 4) (z : CurvatureCoordinateSpace4)
    (hq : ∀ᶠ y in nhds z, 0 < q y)
    (hsource : ∀ᶠ y in nhds z,
      pullCovectorToPrincipalFrame (L y)⁻¹ (v y) source ≠ 0)
    (hchannels : ∀ᶠ y in nhds z,
      curvatureSeedCanonicalChannelField L q y =
        canonicalPhysicalSeedChannels (Real.sqrt (2 * q y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (v y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (omega y))
          (a * (c y ^ 2 - s y ^ 2)) (a * (2 * c y * s y)))
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z)
    (hunit : c z ^ 2 + s z ^ 2 = 1)
    (hdc : scalarFieldCoordinateFDeriv c z = (-s z) • omega z)
    (hds : scalarFieldCoordinateFDeriv s z = c z • omega z) :
    IsPhysicalConstantCouplingChannel (Real.sqrt (2 * q z))
      (pullCovectorToPrincipalFrame (L z)⁻¹ (v z))
      (pullCovectorToPrincipalFrame (L z)⁻¹
        (curvatureSeedCosineCoordinateDerivative L q v source z))
      (curvatureSeedCanonicalChannelField L q z) a := by
  let vp : CurvatureCoordinateSpace4 → OneForm4 := fun y =>
    pullCovectorToPrincipalFrame (L y)⁻¹ (v y)
  let wp : CurvatureCoordinateSpace4 → OneForm4 := fun y =>
    pullCovectorToPrincipalFrame (L y)⁻¹ (omega y)
  let A : CurvatureCoordinateSpace4 → ℝ := fun y =>
    a * (c y ^ 2 - s y ^ 2)
  let B : CurvatureCoordinateSpace4 → ℝ := fun y =>
    a * (2 * c y * s y)
  let eta : CurvatureCoordinateSpace4 → OneForm4 := fun y =>
    effectiveComplexionOneForm (wp y)
      (canonicalPrincipalReflectionCovector (vp y)) (B y)
  have heffective : ∀ᶠ y in nhds z,
      curvatureSeedCanonicalChannelField L q y =
        canonicalComplexionCouplingChannels (Real.sqrt (2 * q y))
          (vp y) (eta y) (A y) := by
    filter_upwards [hchannels] with y hy
    calc
      curvatureSeedCanonicalChannelField L q y =
          canonicalPhysicalSeedChannels (Real.sqrt (2 * q y))
            (vp y) (wp y) (A y) (B y) := by
              simpa [vp, wp, A, B] using hy
      _ = canonicalFullComplexionCouplingChannels (Real.sqrt (2 * q y))
            (vp y) (wp y) (A y) (B y) :=
              canonicalPhysicalSeedChannels_eq_full _ _ _ _ _
      _ = canonicalComplexionCouplingChannels (Real.sqrt (2 * q y))
            (vp y) (eta y) (A y) := by rfl
  have hdA :=
    curvatureSeedCosineCoordinateDerivative_eq_doubleAngleCosine_of_physicalGerm
      L q v eta a c s source z hq (by simpa [vp] using hsource)
      heffective hc hs
  have hdAcoordinate :
      curvatureSeedCosineCoordinateDerivative L q v source z =
        (-2 * B z) • omega z := by
    rw [hdA]
    simpa [B] using doubleAngleCosineFirstDerivative_eq
      a (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) (omega z) hdc hds
  have hdAprincipal :
      pullCovectorToPrincipalFrame (L z)⁻¹
          (curvatureSeedCosineCoordinateDerivative L q v source z) =
        (-2 * B z) • wp z := by
    rw [hdAcoordinate, pullCovectorToPrincipalFrame_smul]
  refine ⟨eta z, A z, B z, c z, s z, ?_, ?_, ?_, hunit, ?_⟩
  · have hzchannels := hchannels.self_of_nhds
    calc
      curvatureSeedCanonicalChannelField L q z =
          canonicalPhysicalSeedChannels (Real.sqrt (2 * q z))
            (vp z) (wp z) (A z) (B z) := by
              simpa [vp, wp, A, B] using hzchannels
      _ = canonicalFullComplexionCouplingChannels (Real.sqrt (2 * q z))
            (vp z) (wp z) (A z) (B z) :=
              canonicalPhysicalSeedChannels_eq_full _ _ _ _ _
      _ = canonicalComplexionCouplingChannels (Real.sqrt (2 * q z))
            (vp z) (eta z) (A z) := by rfl
  · rfl
  · rfl
  · exact nextOrderSineCouplingEquation_eq_zero _ _ _ (wp z) (B z)
      hdAprincipal rfl

/-- Complete first-channel acceptance for two source components throughout an
open patch makes their quotient scalar fields equal near every patch point. -/
theorem curvatureSeedCosineFields_eventuallyEq_of_patchCandidates
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (source source' : Fin 4) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hqPos : ∀ y ∈ U, 0 < q y)
    (hsource : ∀ y ∈ U,
      IsCanonicalEffectiveChannelCandidate (Real.sqrt (2 * q y))
        (pullCovectorToPrincipalFrame (L y)⁻¹ (v y))
        (curvatureSeedCanonicalChannelField L q y) source)
    (hsource' : ∀ y ∈ U,
      IsCanonicalEffectiveChannelCandidate (Real.sqrt (2 * q y))
        (pullCovectorToPrincipalFrame (L y)⁻¹ (v y))
        (curvatureSeedCanonicalChannelField L q y) source') :
    curvatureSeedCosineField L q v source =ᶠ[nhds z]
      curvatureSeedCosineField L q v source' := by
  filter_upwards [hopen.mem_nhds hz] with y hy
  unfold curvatureSeedCosineField
  apply canonicalEffectiveChannelCandidates_cosine_eq
  · exact Real.sqrt_ne_zero'.mpr
      (mul_pos (by norm_num) (hqPos y hy))
  · exact hsource y hy
  · exact hsource' y hy

/-- Patch acceptance of two full fourth-order choices supplies the
neighborhood equality needed for source-independent `dA`. -/
theorem curvatureSeedCosineCoordinateDerivatives_eq_of_patchAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (choice choice' : FourthOrderComponentChoice)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hqPos : ∀ y ∈ U, 0 < q y)
    (hchoice : ∀ y ∈ U,
      IsCurvatureSeedFourthOrderCandidateAt L q v y choice)
    (hchoice' : ∀ y ∈ U,
      IsCurvatureSeedFourthOrderCandidateAt L q v y choice') :
    curvatureSeedCosineCoordinateDerivative L q v choice.1 z =
      curvatureSeedCosineCoordinateDerivative L q v choice'.1 z := by
  apply curvatureSeedCosineCoordinateDerivative_eq_of_eventuallyEq
  apply curvatureSeedCosineFields_eventuallyEq_of_patchCandidates
    L q v choice.1 choice'.1 z hopen hz hqPos
  · intro y hy
    exact (hchoice y hy).2.1
  · intro y hy
    exact (hchoice' y hy).2.1

/-- **Patch-level finite-branch confluence.** On the positive-`q` open patch,
any two choices accepted throughout the patch return the same squared
coupling at every point.  This includes independence of both the first-order
source component and the next-order wedge component. -/
theorem curvatureSeedFourthOrderCouplingSqCandidates_eq_of_patchAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (choice choice' : FourthOrderComponentChoice)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hqPos : ∀ y ∈ U, 0 < q y)
    (hchoice : ∀ y ∈ U,
      IsCurvatureSeedFourthOrderCandidateAt L q v y choice)
    (hchoice' : ∀ y ∈ U,
      IsCurvatureSeedFourthOrderCandidateAt L q v y choice') :
    curvatureSeedFourthOrderCouplingSqCandidateAt L q v z choice =
      curvatureSeedFourthOrderCouplingSqCandidateAt L q v z choice' := by
  have hdA :=
    curvatureSeedCosineCoordinateDerivatives_eq_of_patchAcceptance
      L q v choice choice' z hopen hz hqPos hchoice hchoice'
  unfold curvatureSeedFourthOrderCouplingSqCandidateAt
  rw [hdA]
  have hchoiceAt := hchoice z hz
  change IsTransportedSeedFourthOrderCandidate
    (L z) (L z)⁻¹ (matrixFieldCoordinateFDeriv4 L z) (q z)
    (scalarFieldCoordinateFDeriv q z) (v z)
    (curvatureSeedCosineCoordinateDerivative L q v choice.1 z)
    choice at hchoiceAt
  rw [hdA] at hchoiceAt
  exact transportedSeedFourthOrderCouplingSqCandidates_eq
    (L z) (L z)⁻¹ (matrixFieldCoordinateFDeriv4 L z) (q z)
    (scalarFieldCoordinateFDeriv q z) (v z)
    (curvatureSeedCosineCoordinateDerivative L q v choice'.1 z)
    choice choice' hchoiceAt
    (hchoice' z hz)

/-- Specialization of the matter-free detector to one of the repository's
two curvature-reconstructed scalar branches. -/
def IsCurvatureBranchFourthOrderCandidateAt
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : Prop :=
  IsCurvatureSeedFourthOrderCandidateAt L q
    (C.branchScalarOneFormValue branch) z choice

/-- Finite fourth-order choice set carried by a selected curvature scalar
branch. -/
noncomputable def acceptedCurvatureBranchFourthOrderChoicesAt
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) :
    Finset FourthOrderComponentChoice :=
  acceptedCurvatureSeedFourthOrderChoicesAt L q
    (C.branchScalarOneFormValue branch) z

/-- Squared coupling returned by one accepted choice on a selected curvature
scalar branch. -/
noncomputable def curvatureBranchFourthOrderCouplingSqCandidateAt
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  curvatureSeedFourthOrderCouplingSqCandidateAt L q
    (C.branchScalarOneFormValue branch) z choice

/-- Membership statement for the selected curvature branch detector. -/
theorem mem_acceptedCurvatureBranchFourthOrderChoicesAt_iff
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) :
    choice ∈ acceptedCurvatureBranchFourthOrderChoicesAt
        L q C branch z ↔
      IsCurvatureBranchFourthOrderCandidateAt
        L q C branch z choice := by
  exact mem_acceptedCurvatureSeedFourthOrderChoicesAt_iff
    L q (C.branchScalarOneFormValue branch) z choice

/-- **Curvature-branch detector confluence.** If two finite choices survive
throughout the open positive-`q` patch, their fourth-order coupling squares
agree pointwise. -/
theorem curvatureBranchFourthOrderCouplingSqCandidates_eq_of_patchAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (choice choice' : FourthOrderComponentChoice)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hqPos : ∀ y ∈ U, 0 < q y)
    (hchoice : ∀ y ∈ U,
      IsCurvatureBranchFourthOrderCandidateAt L q C branch y choice)
    (hchoice' : ∀ y ∈ U,
      IsCurvatureBranchFourthOrderCandidateAt L q C branch y choice') :
    curvatureBranchFourthOrderCouplingSqCandidateAt
        L q C branch z choice =
      curvatureBranchFourthOrderCouplingSqCandidateAt
        L q C branch z choice' := by
  exact curvatureSeedFourthOrderCouplingSqCandidates_eq_of_patchAcceptance
    L q (C.branchScalarOneFormValue branch) choice choice' z
    hopen hz hqPos hchoice hchoice'

/-- Principal coframe constructed from the actual selected-branch residual,
its curvature projectors, and four fixed local Gram--Schmidt probes.  Neither
the residual nor the frame is independently supplied to the detector. -/
noncomputable def curvatureBranchPrincipalCoframeField
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4) :
    CurvatureCoordinateSpace4 → Matrix4 :=
  let S := curvatureMaxwellResidualField R
    (C.scalarContribution gInv branch)
  let P := curvatureMaxwellMinusProjectorField S qSq
  let Q := curvatureMaxwellPlusProjectorField S qSq
  smoothPrincipalCoframeMatrix
    (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1)

/-- Pointwise fourth-order detector after constructing both the Maxwell
residual and the principal coframe from the Ricci/scalar branch data. -/
def IsRicciBranchFourthOrderCandidateAt
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : Prop :=
  IsCurvatureBranchFourthOrderCandidateAt
    (curvatureBranchPrincipalCoframeField
      g R gInv qSq C branch u0 u1 v0 v1)
    (positiveMaxwellMagnitudeFromSquare qSq)
    C branch z choice

/-- Finite detector choice set after the residual and principal frame have
been constructed from one Ricci scalar branch. -/
noncomputable def acceptedRicciBranchFourthOrderChoicesAt
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    Finset FourthOrderComponentChoice :=
  acceptedCurvatureBranchFourthOrderChoicesAt
    (curvatureBranchPrincipalCoframeField
      g R gInv qSq C branch u0 u1 v0 v1)
    (positiveMaxwellMagnitudeFromSquare qSq)
    C branch z

/-- Squared coupling produced after constructing the residual and principal
coframe from a Ricci scalar branch. -/
noncomputable def ricciBranchFourthOrderCouplingSqCandidateAt
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  curvatureBranchFourthOrderCouplingSqCandidateAt
    (curvatureBranchPrincipalCoframeField
      g R gInv qSq C branch u0 u1 v0 v1)
    (positiveMaxwellMagnitudeFromSquare qSq)
    C branch z choice

/-- Membership statement for the Ricci-branch finite detector. -/
theorem mem_acceptedRicciBranchFourthOrderChoicesAt_iff
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) :
    choice ∈ acceptedRicciBranchFourthOrderChoicesAt
        g R gInv qSq C branch u0 u1 v0 v1 z ↔
      IsRicciBranchFourthOrderCandidateAt
        g R gInv qSq C branch u0 u1 v0 v1 z choice := by
  exact mem_acceptedCurvatureBranchFourthOrderChoicesAt_iff
    (curvatureBranchPrincipalCoframeField
      g R gInv qSq C branch u0 u1 v0 v1)
    (positiveMaxwellMagnitudeFromSquare qSq)
    C branch z choice

/-- **Ricci-branch finite-detector confluence.** Once the pointwise scalar
branch, residual, and principal frame have been constructed, all finite
choices accepted throughout the open positive-square patch return the same
squared coupling. -/
theorem ricciBranchFourthOrderCouplingSqCandidates_eq_of_patchAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (choice choice' : FourthOrderComponentChoice)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hqSqPos : ∀ y ∈ U, 0 < qSq y)
    (hchoice : ∀ y ∈ U,
      IsRicciBranchFourthOrderCandidateAt
        g R gInv qSq C branch u0 u1 v0 v1 y choice)
    (hchoice' : ∀ y ∈ U,
      IsRicciBranchFourthOrderCandidateAt
        g R gInv qSq C branch u0 u1 v0 v1 y choice') :
    ricciBranchFourthOrderCouplingSqCandidateAt
        g R gInv qSq C branch u0 u1 v0 v1 z choice =
      ricciBranchFourthOrderCouplingSqCandidateAt
        g R gInv qSq C branch u0 u1 v0 v1 z choice' := by
  apply curvatureBranchFourthOrderCouplingSqCandidates_eq_of_patchAcceptance
    (curvatureBranchPrincipalCoframeField
      g R gInv qSq C branch u0 u1 v0 v1)
    (positiveMaxwellMagnitudeFromSquare qSq)
    C branch choice choice' z hopen hz
  · intro y hy
    exact positiveMaxwellMagnitudeFromSquare_pos qSq y (hqSqPos y hy)
  · exact hchoice
  · exact hchoice'

/-- Coordinate matrix of an actual continuous metric bilinear-form field in
the standard coordinate directions. -/
noncomputable def coordinateMetricMatrixField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  fun i j => g z (curvatureCoordinateDirection i)
    (curvatureCoordinateDirection j)

/-- The coordinate metric matrix represents exactly the original continuous
bilinear form after forgetting continuity. -/
theorem coordinateMetricMatrixField4_toBilin'
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    Matrix.toBilin' (coordinateMetricMatrixField4 g z) =
      continuousBilinFormToBilin (g z) := by
  rw [← Matrix.toBilin'_toMatrix'
    (continuousBilinFormToBilin (g z))]
  congr 1
  have hcoord (n : Fin 4) :
      curvatureCoordinateDirection n = Pi.single n 1 := by
    funext k
    simp [curvatureCoordinateDirection, Pi.single_apply]
  ext i j
  simp only [coordinateMetricMatrixField4,
    LinearMap.BilinForm.toMatrix'_apply]
  rw [hcoord i, hcoord j]
  rfl

/-- Symmetry of the actual continuous metric is inherited by its coordinate
matrix. -/
theorem coordinateMetricMatrixField4_transpose_eq_self
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm) :
    (coordinateMetricMatrixField4 g z).transpose =
      coordinateMetricMatrixField4 g z := by
  ext i j
  simp only [Matrix.transpose_apply, coordinateMetricMatrixField4]
  exact hgsymm.eq _ _

/-- Actual first coordinate jet of the metric matrix field. -/
noncomputable def actualCoordinateMetricJet1Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : CoordinateMetricJet1 (Fin 4) :=
  fun r i j => scalarFieldCoordinateFDeriv
    (fun y => coordinateMetricMatrixField4 g y i j) z r

/-- Actual second coordinate jet, obtained by differentiating the actual
first coordinate jet rather than accepting an arbitrary array. -/
noncomputable def actualCoordinateMetricJet2Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : CoordinateMetricJet2 (Fin 4) :=
  fun r s i j => scalarFieldCoordinateFDeriv
    (fun y => actualCoordinateMetricJet1Field4 g y s i j) z r

/-- Covariant Ricci matrix computed definitionally from the actual metric
two-jet and its constructed matrix inverse. -/
noncomputable def actualCoordinateRicciCovariantField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  fun i j => coordinateRicci ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
    (actualCoordinateMetricJet1Field4 g z)
    (actualCoordinateMetricJet2Field4 g z) i j

/-- Regression lock: the inverse supplied to the coordinate Ricci formula is
the matrix inverse, not the entrywise inverse inherited by the underlying
function type.  The explicit type ascription in this statement is
scientifically significant. -/
theorem actualCoordinateRicciCovariantField4_uses_matrixInverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    actualCoordinateRicciCovariantField4 g z =
      fun i j => coordinateRicci
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (actualCoordinateMetricJet2Field4 g z) i j := by
  rfl

/-- Actual mixed Ricci endomorphism `R^i_j`, constructed from the metric
alone. -/
noncomputable def actualMixedRicciField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  (coordinateMetricMatrixField4 g z)⁻¹ *
    actualCoordinateRicciCovariantField4 g z

/-- Curvature-only protected squared magnitude reconstructed from the
characteristic coefficients of the actual mixed Ricci endomorphism. -/
noncomputable def actualRicciReconstructedQSqField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  reconstructedQSq
    (CharacteristicData.ofEndomorphism
      (Matrix.toLin' (actualMixedRicciField4 g z)))

/-- Full characteristic coefficient field of the actual mixed Ricci
endomorphism. -/
noncomputable def actualRicciCharacteristicDataField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : CharacteristicData :=
  CharacteristicData.ofEndomorphism
    (Matrix.toLin' (actualMixedRicciField4 g z))

/-- Discriminant of the complementary quadratic factor reconstructed from
the actual Ricci characteristic coefficients. -/
noncomputable def actualRicciComplementaryDiscriminantField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  let d := actualRicciCharacteristicDataField4 g z
  d.e1 ^ 2 + 4 * reconstructedResidualConstant d

/-- Lower labeled root of the reconstructed complementary quadratic. -/
noncomputable def actualRicciComplementaryRootAField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  let d := actualRicciCharacteristicDataField4 g z
  (d.e1 - Real.sqrt (actualRicciComplementaryDiscriminantField4 g z)) / 2

/-- Upper labeled root of the reconstructed complementary quadratic. -/
noncomputable def actualRicciComplementaryRootBField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  let d := actualRicciCharacteristicDataField4 g z
  (d.e1 + Real.sqrt (actualRicciComplementaryDiscriminantField4 g z)) / 2

/-- Positive protected root reconstructed from the actual Ricci
characteristic coefficients. -/
noncomputable def actualRicciProtectedRootField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  Real.sqrt (actualRicciReconstructedQSqField4 g z)

/-- Polynomial projector onto the lower complementary Ricci root. -/
noncomputable def actualRicciComplementaryProjectorAField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4) :
    CurvatureCoordinateSpace4 → Matrix4 :=
  matrixFourRootProjectorField (actualMixedRicciField4 g)
    (actualRicciComplementaryRootAField4 g)
    (fun z => -actualRicciProtectedRootField4 g z)
    (actualRicciComplementaryRootBField4 g)
    (actualRicciProtectedRootField4 g)

/-- Polynomial projector onto the upper complementary Ricci root. -/
noncomputable def actualRicciComplementaryProjectorBField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4) :
    CurvatureCoordinateSpace4 → Matrix4 :=
  matrixFourRootProjectorField (actualMixedRicciField4 g)
    (actualRicciComplementaryRootBField4 g)
    (actualRicciComplementaryRootAField4 g)
    (fun z => -actualRicciProtectedRootField4 g z)
    (actualRicciProtectedRootField4 g)

/-- The two explicitly labeled complementary roots sum to the actual Ricci
trace coefficient whenever the discriminant is nonnegative. -/
theorem actualRicciComplementaryRoots_sum
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    actualRicciComplementaryRootAField4 g z +
        actualRicciComplementaryRootBField4 g z =
      (actualRicciCharacteristicDataField4 g z).e1 := by
  unfold actualRicciComplementaryRootAField4
    actualRicciComplementaryRootBField4
  ring

/-- Strictly positive complementary discriminant makes the two actual-Ricci
root formulas distinct. -/
theorem actualRicciComplementaryRoots_ne
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hdisc : 0 < actualRicciComplementaryDiscriminantField4 g z) :
    actualRicciComplementaryRootAField4 g z ≠
      actualRicciComplementaryRootBField4 g z := by
  intro heq
  have hsqrt : Real.sqrt
      (actualRicciComplementaryDiscriminantField4 g z) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hdisc
  unfold actualRicciComplementaryRootAField4
    actualRicciComplementaryRootBField4 at heq
  have : Real.sqrt (actualRicciComplementaryDiscriminantField4 g z) = 0 := by
    linarith
  exact hsqrt this

/-- **Actual-metric scalar-branch constructor.** On the explicit generic
regularity, root-gap, radicand, and fixed-probe sign branch, the actual metric
Ricci coefficients and their polynomial projectors construct the complete
two-candidate scalar-branch certificate.  No root, projector, amplitude, or
derivative field is supplied independently. -/
noncomputable def actualMetricScalarBranchComponentPatch4
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (probeA probeB : CurvatureCoordinateSpace4)
    (hopen : IsOpen U)
    (ha : ContDiffOn ℝ 1 (actualRicciComplementaryRootAField4 g) U)
    (hb : ContDiffOn ℝ 1 (actualRicciComplementaryRootBField4 g) U)
    (hqSq : ContDiffOn ℝ 1 (actualRicciReconstructedQSqField4 g) U)
    (hg : ContDiffOn ℝ 1 g U)
    (hPA : MatrixFieldContDiffOn 1 U
      (actualRicciComplementaryProjectorAField4 g))
    (hPB : MatrixFieldContDiffOn 1 U
      (actualRicciComplementaryProjectorBField4 g))
    (hab : ∀ z ∈ U,
      actualRicciComplementaryRootAField4 g z ≠
        actualRicciComplementaryRootBField4 g z)
    (hposA : ∀ z ∈ U, 0 <
      2 * (-1 : ℝ) * reconstructedDiagonalAField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) z)
    (hposB : ∀ z ∈ U, 0 <
      2 * (1 : ℝ) * reconstructedDiagonalBField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) z)
    (htime : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector
        (actualRicciComplementaryProjectorAField4 g) probeA)
      (smoothMatrixProjectedVector
        (actualRicciComplementaryProjectorAField4 g) probeA) z < 0)
    (hspace : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector
        (actualRicciComplementaryProjectorBField4 g) probeB)
      (smoothMatrixProjectedVector
        (actualRicciComplementaryProjectorBField4 g) probeB) z) :
    CurvatureScalarBranchComponentPatch4 U :=
  CurvatureScalarBranchComponentPatch4.ofConcreteFixedProbeCurvatureFields
    (-1) 1
    (actualRicciComplementaryRootAField4 g)
    (actualRicciComplementaryRootBField4 g)
    (actualRicciReconstructedQSqField4 g) g
    (actualRicciComplementaryProjectorAField4 g)
    (actualRicciComplementaryProjectorBField4 g)
    probeA probeB hopen ha hb hqSq hg hPA hPB hab hposA hposB
    htime hspace

/-- Compatibility obstruction saying that a supplied finite scalar-branch
certificate is genuinely tied to the actual metric Ricci field.  Its
reconstructed `qSq` must equal the characteristic formula, and its rank-one
contribution must solve the full reconstruction equation. -/
def IsActualMetricCurvatureBranchPatch4
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) : Prop :=
  ∀ z ∈ U,
    (C.jet z).qSq = actualRicciReconstructedQSqField4 g z ∧
    let R := actualMixedRicciField4 g z
    let V := C.scalarContribution
      (fun y => (coordinateMetricMatrixField4 g y)⁻¹) branch z
    let traceV := scalarContributionTraceField
      (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
      (C.branchScalarOneFormValue branch) z
    R * V + V * R - traceV • V =
      R * R - actualRicciReconstructedQSqField4 g z • (1 : Matrix4)

/-- The compatibility obstruction makes the selected branch's actual
metric-derived residual obey the Maxwell square law; no residual or square
law is separately assumed. -/
theorem actualMetricCurvatureBranch_residual_sq
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hcompat : IsActualMetricCurvatureBranchPatch4 g C branch)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    let gInv := fun y => (coordinateMetricMatrixField4 g y)⁻¹
    let S := curvatureMaxwellResidualField (actualMixedRicciField4 g)
      (C.scalarContribution gInv branch)
    S z * S z =
      actualRicciReconstructedQSqField4 g z • (1 : Matrix4) := by
  dsimp only
  apply curvatureMaxwellResidualField_sq_of_branchScalarContribution
    C (actualMixedRicciField4 g)
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualRicciReconstructedQSqField4 g) branch z
  exact (hcompat z hz).2

/-- Positive reconstructed square plus actual-metric branch compatibility
therefore supplies the complete idempotent/complementary principal-projector
algebra used by the constructed coframe. -/
theorem actualMetricCurvatureBranch_principalProjectors_structural
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hcompat : IsActualMetricCurvatureBranchPatch4 g C branch)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U)
    (hqSqPos : 0 < actualRicciReconstructedQSqField4 g z) :
    let gInv := fun y => (coordinateMetricMatrixField4 g y)⁻¹
    let S := curvatureMaxwellResidualField (actualMixedRicciField4 g)
      (C.scalarContribution gInv branch)
    let P := curvatureMaxwellMinusProjectorField S
      (actualRicciReconstructedQSqField4 g) z
    let Q := curvatureMaxwellPlusProjectorField S
      (actualRicciReconstructedQSqField4 g) z
    P * P = P ∧ Q * Q = Q ∧ P * Q = 0 ∧ P + Q = 1 := by
  dsimp only
  apply curvatureMaxwellPrincipalProjectorFields_structural
  · exact hqSqPos
  · exact actualMetricCurvatureBranch_residual_sq
      g C branch hcompat z hz

/-- Fourth-order detector predicate whose geometric tensor inputs `R`,
`gInv`, `qSq`, the Maxwell residual, projectors, coframe, and all required
derivatives are constructed from the actual metric.  The remaining `C` and
fixed probes are finite/local scalar-branch auxiliaries guarded by the
compatibility predicate above. -/
def IsActualMetricRicciBranchFourthOrderCandidateAt
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : Prop :=
  IsRicciBranchFourthOrderCandidateAt g
    (actualMixedRicciField4 g)
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualRicciReconstructedQSqField4 g)
    C branch u0 u1 v0 v1 z choice

/-- Finite accepted set of the actual-metric Ricci-branch detector. -/
noncomputable def acceptedActualMetricRicciBranchFourthOrderChoicesAt
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    Finset FourthOrderComponentChoice :=
  acceptedRicciBranchFourthOrderChoicesAt g
    (actualMixedRicciField4 g)
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualRicciReconstructedQSqField4 g)
    C branch u0 u1 v0 v1 z

/-- Squared-coupling candidate returned from the actual metric and one
compatible scalar-branch/probe choice. -/
noncomputable def actualMetricRicciBranchFourthOrderCouplingSqCandidateAt
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  ricciBranchFourthOrderCouplingSqCandidateAt g
    (actualMixedRicciField4 g)
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualRicciReconstructedQSqField4 g)
    C branch u0 u1 v0 v1 z choice

/-- Membership statement for the actual-metric Ricci-branch detector. -/
theorem mem_acceptedActualMetricRicciBranchFourthOrderChoicesAt_iff
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) :
    choice ∈ acceptedActualMetricRicciBranchFourthOrderChoicesAt
        g C branch u0 u1 v0 v1 z ↔
      IsActualMetricRicciBranchFourthOrderCandidateAt
        g C branch u0 u1 v0 v1 z choice := by
  exact mem_acceptedRicciBranchFourthOrderChoicesAt_iff g
    (actualMixedRicciField4 g)
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualRicciReconstructedQSqField4 g)
    C branch u0 u1 v0 v1 z choice

/-- Component-choice confluence for the detector whose curvature tensors and
principal seed are all constructed from the actual metric. -/
theorem actualMetricRicciBranchFourthOrderCouplingSqCandidates_eq_of_patchAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (choice choice' : FourthOrderComponentChoice)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hqSqPos : ∀ y ∈ U, 0 < actualRicciReconstructedQSqField4 g y)
    (hchoice : ∀ y ∈ U,
      IsActualMetricRicciBranchFourthOrderCandidateAt
        g C branch u0 u1 v0 v1 y choice)
    (hchoice' : ∀ y ∈ U,
      IsActualMetricRicciBranchFourthOrderCandidateAt
        g C branch u0 u1 v0 v1 y choice') :
    actualMetricRicciBranchFourthOrderCouplingSqCandidateAt
        g C branch u0 u1 v0 v1 z choice =
      actualMetricRicciBranchFourthOrderCouplingSqCandidateAt
        g C branch u0 u1 v0 v1 z choice' := by
  exact ricciBranchFourthOrderCouplingSqCandidates_eq_of_patchAcceptance g
    (actualMixedRicciField4 g)
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualRicciReconstructedQSqField4 g)
    C branch u0 u1 v0 v1 choice choice' z hopen hz hqSqPos
    hchoice hchoice'

/-- One finite raw choice for the completely metric-constructed detector.
The six probe indices select coordinate-basis probes for the two scalar
eigenlines and the two Maxwell principal planes.  The Lorentzian pivot recipe
then extracts a timelike vector algebraically from the selected pair, so no
individual projected coordinate vector is assumed timelike.
`relativeMinus=false` means `alpha+beta`, while `true` means `alpha-beta`. -/
structure ActualMetricDetectorChoice4 where
  scalarTimelikeProbe : Fin 4
  scalarSpacelikeProbe : Fin 4
  maxwellMinusProbe0 : Fin 4
  maxwellMinusProbe1 : Fin 4
  maxwellMinusPivotRecipe : LorentzianPivotRecipe
  maxwellPlusProbe0 : Fin 4
  maxwellPlusProbe1 : Fin 4
  relativeMinus : Bool
  orientationReverse : Bool
  channel : FourthOrderComponentChoice
  deriving DecidableEq

/-- Explicit finite enumeration of the raw metric-detector choices.  Writing
the enumeration out keeps the finite search space transparent and avoids
depending on a deeply nested automatically synthesized product instance. -/
noncomputable def allActualMetricDetectorChoices4 :
    Finset ActualMetricDetectorChoice4 := by
  classical
  exact Finset.univ.biUnion fun scalarTimelikeProbe : Fin 4 =>
    Finset.univ.biUnion fun scalarSpacelikeProbe : Fin 4 =>
      Finset.univ.biUnion fun maxwellMinusProbe0 : Fin 4 =>
        Finset.univ.biUnion fun maxwellMinusProbe1 : Fin 4 =>
          Finset.univ.biUnion fun maxwellMinusPivotRecipe :
              LorentzianPivotRecipe =>
            Finset.univ.biUnion fun maxwellPlusProbe0 : Fin 4 =>
              Finset.univ.biUnion fun maxwellPlusProbe1 : Fin 4 =>
                Finset.univ.biUnion fun relativeMinus : Bool =>
                  Finset.univ.biUnion fun orientationReverse : Bool =>
                    Finset.univ.image fun channel : FourthOrderComponentChoice =>
                      { scalarTimelikeProbe := scalarTimelikeProbe
                        scalarSpacelikeProbe := scalarSpacelikeProbe
                        maxwellMinusProbe0 := maxwellMinusProbe0
                        maxwellMinusProbe1 := maxwellMinusProbe1
                        maxwellMinusPivotRecipe := maxwellMinusPivotRecipe
                        maxwellPlusProbe0 := maxwellPlusProbe0
                        maxwellPlusProbe1 := maxwellPlusProbe1
                        relativeMinus := relativeMinus
                        orientationReverse := orientationReverse
                        channel := channel }

set_option maxHeartbeats 800000 in
/-- Every raw detector choice occurs in the explicit finite enumeration. -/
theorem mem_allActualMetricDetectorChoices4
    (choice : ActualMetricDetectorChoice4) :
    choice ∈ allActualMetricDetectorChoices4 := by
  classical
  rcases choice with
    ⟨scalarTimelikeProbe, scalarSpacelikeProbe,
      maxwellMinusProbe0, maxwellMinusProbe1,
      maxwellMinusPivotRecipe,
      maxwellPlusProbe0, maxwellPlusProbe1, relativeMinus,
      orientationReverse, channel⟩
  cases maxwellMinusPivotRecipe <;> cases relativeMinus <;>
    cases orientationReverse <;>
    simp [allActualMetricDetectorChoices4]

/-- Replace only the raw channel-component choice, leaving the scalar and
principal-frame branch fixed. -/
def ActualMetricDetectorChoice4.withChannel
    (choice : ActualMetricDetectorChoice4)
    (channel : FourthOrderComponentChoice) : ActualMetricDetectorChoice4 :=
  { choice with channel := channel }

/-- Replace only the finite spacetime-orientation bit. -/
def ActualMetricDetectorChoice4.withOrientationReverse
    (choice : ActualMetricDetectorChoice4)
    (reverse : Bool) : ActualMetricDetectorChoice4 :=
  { choice with orientationReverse := reverse }

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_value
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).orientationReverse = reverse := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_channel
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).channel = choice.channel := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_scalarTimelikeProbe
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).scalarTimelikeProbe =
      choice.scalarTimelikeProbe := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_scalarSpacelikeProbe
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).scalarSpacelikeProbe =
      choice.scalarSpacelikeProbe := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_maxwellMinusProbe0
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).maxwellMinusProbe0 =
      choice.maxwellMinusProbe0 := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_maxwellMinusProbe1
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).maxwellMinusProbe1 =
      choice.maxwellMinusProbe1 := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_maxwellMinusPivotRecipe
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).maxwellMinusPivotRecipe =
      choice.maxwellMinusPivotRecipe := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_maxwellPlusProbe0
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).maxwellPlusProbe0 =
      choice.maxwellPlusProbe0 := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_maxwellPlusProbe1
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).maxwellPlusProbe1 =
      choice.maxwellPlusProbe1 := rfl

@[simp] theorem ActualMetricDetectorChoice4.withOrientationReverse_relativeMinus
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    (choice.withOrientationReverse reverse).relativeMinus =
      choice.relativeMinus := rfl

/-- Replace only the two finite scalar-eigenline probes, retaining the
relative-sign branch, Maxwell frame, and fourth-order component. -/
def ActualMetricDetectorChoice4.withScalarProbes
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) : ActualMetricDetectorChoice4 :=
  { choice with
      scalarTimelikeProbe := i
      scalarSpacelikeProbe := j }

@[simp] theorem ActualMetricDetectorChoice4.withScalarProbes_timelike
    (choice : ActualMetricDetectorChoice4) (i j : Fin 4) :
    (choice.withScalarProbes i j).scalarTimelikeProbe = i := rfl

@[simp] theorem ActualMetricDetectorChoice4.withScalarProbes_spacelike
    (choice : ActualMetricDetectorChoice4) (i j : Fin 4) :
    (choice.withScalarProbes i j).scalarSpacelikeProbe = j := rfl

@[simp] theorem ActualMetricDetectorChoice4.withScalarProbes_relativeMinus
    (choice : ActualMetricDetectorChoice4) (i j : Fin 4) :
    (choice.withScalarProbes i j).relativeMinus = choice.relativeMinus := rfl

@[simp] theorem ActualMetricDetectorChoice4.withScalarProbes_channel
    (choice : ActualMetricDetectorChoice4) (i j : Fin 4) :
    (choice.withScalarProbes i j).channel = choice.channel := rfl

/-- Replace only the finite Lorentzian Maxwell coordinate pair and pivot
recipe.  The scalar branch, physical residual, positive-plane probes, and
fourth-order channel remain unchanged. -/
def ActualMetricDetectorChoice4.withMaxwellMinusFrame
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) :
    ActualMetricDetectorChoice4 :=
  { choice with
      maxwellMinusProbe0 := i
      maxwellMinusProbe1 := j
      maxwellMinusPivotRecipe := recipe }

/-- Replace the complete finite Maxwell principal-frame choice while retaining
the scalar branch and fourth-order channel. -/
def ActualMetricDetectorChoice4.withMaxwellFrame
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    ActualMetricDetectorChoice4 :=
  { choice with
      maxwellMinusProbe0 := i
      maxwellMinusProbe1 := j
      maxwellMinusPivotRecipe := recipe
      maxwellPlusProbe0 := k
      maxwellPlusProbe1 := l }

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellMinusFrame_probe0
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) :
    (choice.withMaxwellMinusFrame i j recipe).maxwellMinusProbe0 = i := rfl

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellMinusFrame_probe1
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) :
    (choice.withMaxwellMinusFrame i j recipe).maxwellMinusProbe1 = j := rfl

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellMinusFrame_recipe
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) :
    (choice.withMaxwellMinusFrame i j recipe).maxwellMinusPivotRecipe =
      recipe := rfl

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellFrame_probe0
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    (choice.withMaxwellFrame i j recipe k l).maxwellMinusProbe0 = i := rfl

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellFrame_probe1
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    (choice.withMaxwellFrame i j recipe k l).maxwellMinusProbe1 = j := rfl

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellFrame_recipe
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    (choice.withMaxwellFrame i j recipe k l).maxwellMinusPivotRecipe =
      recipe := rfl

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellFrame_plusProbe0
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    (choice.withMaxwellFrame i j recipe k l).maxwellPlusProbe0 = k := rfl

@[simp] theorem ActualMetricDetectorChoice4.withMaxwellFrame_plusProbe1
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    (choice.withMaxwellFrame i j recipe k l).maxwellPlusProbe1 = l := rfl

/-- Completely metric-constructed scalar branch jet for one pair of
coordinate-basis probes. -/
noncomputable def actualMetricScalarBranchJetField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (timelikeProbe spacelikeProbe : Fin 4)
    (z : CurvatureCoordinateSpace4) : CurvatureScalarBranchJet4 :=
  concreteFixedProbeCurvatureScalarBranchJet4 (-1) 1
    (actualRicciComplementaryRootAField4 g)
    (actualRicciComplementaryRootBField4 g)
    (actualRicciReconstructedQSqField4 g) g
    (actualRicciComplementaryProjectorAField4 g)
    (actualRicciComplementaryProjectorBField4 g)
    (curvatureCoordinateDirection timelikeProbe)
    (curvatureCoordinateDirection spacelikeProbe) z

/-- One of the two relative-sign scalar covector fields, constructed from
the actual metric and finite probe indices. -/
noncomputable def actualMetricScalarOneFormCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (timelikeProbe spacelikeProbe : Fin 4)
    (relativeMinus : Bool) (z : CurvatureCoordinateSpace4) : OneForm4 :=
  let J := actualMetricScalarBranchJetField4 g
    timelikeProbe spacelikeProbe z
  if relativeMinus then J.vMinus else J.vPlus

/-- Closure obstruction for the selected actual-metric scalar candidate. -/
noncomputable def actualMetricScalarClosureObstruction4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (timelikeProbe spacelikeProbe : Fin 4)
    (relativeMinus : Bool) (z : CurvatureCoordinateSpace4) : Matrix4 :=
  let J := actualMetricScalarBranchJetField4 g
    timelikeProbe spacelikeProbe z
  if relativeMinus then J.dalpha - J.dbeta else J.dalpha + J.dbeta

/-- Rank-one scalar contribution of the selected completely metric-constructed
covector field. -/
noncomputable def actualMetricScalarContributionCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  scalarContributionMatrixField
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus) z

/-- Maxwell residual obtained by subtracting the selected scalar candidate
from the actual mixed Ricci field. -/
noncomputable def actualMetricMaxwellResidualCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  curvatureMaxwellResidualField (actualMixedRicciField4 g)
    (actualMetricScalarContributionCandidateField4 g choice) z

@[simp] theorem actualMetricMaxwellResidualCandidateField4_withMaxwellMinusFrame
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) :
    actualMetricMaxwellResidualCandidateField4 g
        (choice.withMaxwellMinusFrame i j recipe) =
      actualMetricMaxwellResidualCandidateField4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellResidualCandidateField4_withMaxwellFrame
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    actualMetricMaxwellResidualCandidateField4 g
        (choice.withMaxwellFrame i j recipe k l) =
      actualMetricMaxwellResidualCandidateField4 g choice := by
  rfl

/-- Negative Maxwell principal projector of one actual-metric raw choice. -/
noncomputable def actualMetricMaxwellMinusProjectorCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → Matrix4 :=
  curvatureMaxwellMinusProjectorField
    (actualMetricMaxwellResidualCandidateField4 g choice)
    (actualRicciReconstructedQSqField4 g)

@[simp] theorem actualMetricMaxwellMinusProjectorCandidateField4_withMaxwellMinusFrame
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) :
    actualMetricMaxwellMinusProjectorCandidateField4 g
        (choice.withMaxwellMinusFrame i j recipe) =
      actualMetricMaxwellMinusProjectorCandidateField4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellMinusProjectorCandidateField4_withMaxwellFrame
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    actualMetricMaxwellMinusProjectorCandidateField4 g
        (choice.withMaxwellFrame i j recipe k l) =
      actualMetricMaxwellMinusProjectorCandidateField4 g choice := by
  rfl

/-- Positive Maxwell principal projector of one actual-metric raw choice. -/
noncomputable def actualMetricMaxwellPlusProjectorCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → Matrix4 :=
  curvatureMaxwellPlusProjectorField
    (actualMetricMaxwellResidualCandidateField4 g choice)
    (actualRicciReconstructedQSqField4 g)

@[simp] theorem actualMetricMaxwellPlusProjectorCandidateField4_withMaxwellFrame
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4) :
    actualMetricMaxwellPlusProjectorCandidateField4 g
        (choice.withMaxwellFrame i j recipe k l) =
      actualMetricMaxwellPlusProjectorCandidateField4 g choice := by
  rfl

/-- First projected coordinate probe in the selected Lorentzian Maxwell
principal plane. -/
noncomputable def actualMetricMaxwellMinusProbe0Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 :=
  smoothMatrixProjectedVector
    (actualMetricMaxwellMinusProjectorCandidateField4 g choice)
    (curvatureCoordinateDirection choice.maxwellMinusProbe0)

/-- Second projected coordinate probe in the selected Lorentzian Maxwell
principal plane. -/
noncomputable def actualMetricMaxwellMinusProbe1Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 :=
  smoothMatrixProjectedVector
    (actualMetricMaxwellMinusProjectorCandidateField4 g choice)
    (curvatureCoordinateDirection choice.maxwellMinusProbe1)

/-- Finite metric-dependent timelike-pivot candidate built from the selected
pair of projected coordinate probes. -/
noncomputable def actualMetricMaxwellLorentzPivotCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 :=
  smoothLorentzianPivotCandidate g
    (actualMetricMaxwellMinusProbe0Field4 g choice)
    (actualMetricMaxwellMinusProbe1Field4 g choice)
    choice.maxwellMinusPivotRecipe

/-- Companion field retained for Lorentzian Gram--Schmidt by the selected
finite pivot recipe. -/
noncomputable def actualMetricMaxwellLorentzCompanionCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 :=
  smoothLorentzianPivotCompanion
    (actualMetricMaxwellMinusProbe0Field4 g choice)
    (actualMetricMaxwellMinusProbe1Field4 g choice)
    choice.maxwellMinusPivotRecipe

/-- First projected coordinate probe in the selected spacelike Maxwell
principal plane. -/
noncomputable def actualMetricMaxwellPlusProbe0Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 :=
  smoothMatrixProjectedVector
    (actualMetricMaxwellPlusProjectorCandidateField4 g choice)
    (curvatureCoordinateDirection choice.maxwellPlusProbe0)

/-- Second projected coordinate probe in the selected spacelike Maxwell
principal plane. -/
noncomputable def actualMetricMaxwellPlusProbe1Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 :=
  smoothMatrixProjectedVector
    (actualMetricMaxwellPlusProjectorCandidateField4 g choice)
    (curvatureCoordinateDirection choice.maxwellPlusProbe1)

/- The orientation bit acts only on the final coframe.  These simp lemmas
make that separation explicit, so the upstream algebraic and frame gates can
be transported to either orientation branch without reopening definitions. -/
@[simp] theorem actualMetricMaxwellResidualCandidateField4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellResidualCandidateField4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellResidualCandidateField4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellMinusProjectorCandidateField4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellMinusProjectorCandidateField4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellMinusProjectorCandidateField4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellPlusProjectorCandidateField4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellPlusProjectorCandidateField4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellPlusProjectorCandidateField4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellMinusProbe0Field4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellMinusProbe0Field4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellMinusProbe0Field4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellMinusProbe1Field4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellMinusProbe1Field4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellMinusProbe1Field4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellLorentzPivotCandidateField4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellLorentzPivotCandidateField4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellLorentzPivotCandidateField4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellLorentzCompanionCandidateField4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellLorentzCompanionCandidateField4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellLorentzCompanionCandidateField4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellPlusProbe0Field4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellPlusProbe0Field4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellPlusProbe0Field4 g choice := by
  rfl

@[simp] theorem actualMetricMaxwellPlusProbe1Field4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricMaxwellPlusProbe1Field4 g
        (choice.withOrientationReverse reverse) =
      actualMetricMaxwellPlusProbe1Field4 g choice := by
  rfl

/-- Principal tetrad constructed from one finite actual-metric choice. -/
noncomputable def actualMetricPrincipalTetradCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :=
  smoothPrincipalTetradFromFields g
    (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
    (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)
    (actualMetricMaxwellPlusProbe0Field4 g choice)
    (actualMetricMaxwellPlusProbe1Field4 g choice)

/-- Column frame matrix of the selected principal tetrad. -/
noncomputable def actualMetricPrincipalFrameCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → Matrix4 :=
  smoothPrincipalFrameMatrix
    (actualMetricPrincipalTetradCandidateField4 g choice)

/-- Reflection of the last canonical spacelike coframe leg.  It preserves the
Minkowski metric, fixes the canonical electric `01` seed, reverses the
canonical Hodge `23` seed, and has determinant `-1`. -/
def principalOrientationReflection4 : Matrix4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

/-- Finite orientation action on a true dual coframe. -/
def orientPrincipalCoframe4 (reverse : Bool) (L : Matrix4) : Matrix4 :=
  if reverse then principalOrientationReflection4 * L else L

theorem principalOrientationReflection4_metric :
    principalOrientationReflection4ᵀ * minkowskiMetric *
        principalOrientationReflection4 = minkowskiMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [principalOrientationReflection4, minkowskiMetric,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem principalOrientationReflection4_det :
    Matrix.det principalOrientationReflection4 = -1 := by
  rw [show principalOrientationReflection4 =
    Matrix.diagonal ![(1 : ℝ), 1, 1, -1] by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [principalOrientationReflection4]]
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]

theorem principalOrientationReflection4_electric
    (E : ℝ) :
    transportTwoForm principalOrientationReflection4
        (canonicalMaxwellTwoForm E 0) =
      canonicalMaxwellTwoForm E 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportTwoForm, principalOrientationReflection4,
      canonicalMaxwellTwoForm, Matrix.mul_apply, Fin.sum_univ_succ]

theorem principalOrientationReflection4_hodge
    (E : ℝ) :
    transportTwoForm principalOrientationReflection4
        (canonicalHodgeStar E 0) =
      -canonicalHodgeStar E 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportTwoForm, principalOrientationReflection4,
      canonicalHodgeStar, canonicalMaxwellTwoForm,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- **True dual coframe in an arbitrary coordinate chart.** If `E` is the
column matrix of tetrad vectors, covariant tensor components transport with
`E⁻¹`; the transpose `Eᵀ` is only a row display of the vectors and is not the
dual coframe for a general coordinate metric. -/
noncomputable def actualMetricPrincipalCoframeCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → Matrix4 := fun z =>
  orientPrincipalCoframe4 choice.orientationReverse
    (actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹

/-- A verified pseudo-orthonormal actual-metric tetrad gives the exact
arbitrary-chart coframe/metric congruence needed by the coordinate Hodge
operator. -/
theorem actualMetricPrincipalCoframeCandidate_metric
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hframe : IsPseudoOrthonormalPrincipalTetrad
      (continuousBilinFormToBilin (g z))
      (actualMetricPrincipalTetradCandidateField4 g choice z).1
      (actualMetricPrincipalTetradCandidateField4 g choice z).2) :
    (actualMetricPrincipalCoframeCandidateField4 g choice z)ᵀ *
        minkowskiMetric *
        actualMetricPrincipalCoframeCandidateField4 g choice z =
      coordinateMetricMatrixField4 g z := by
  have hbase := inverse_smoothPrincipalFrameMatrix_metric
    (actualMetricPrincipalTetradCandidateField4 g choice) z
    (continuousBilinFormToBilin (g z))
    (coordinateMetricMatrixField4 g z)
    (coordinateMetricMatrixField4_toBilin' g z) hgsymm hframe
  change ((actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹)ᵀ *
      minkowskiMetric *
      (actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹ =
    coordinateMetricMatrixField4 g z at hbase
  cases horient : choice.orientationReverse
  · simpa [actualMetricPrincipalCoframeCandidateField4,
      orientPrincipalCoframe4, horient] using hbase
  · simp only [actualMetricPrincipalCoframeCandidateField4,
      orientPrincipalCoframe4, horient, ↓reduceIte]
    rw [Matrix.transpose_mul]
    calc
      ((actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹)ᵀ *
          principalOrientationReflection4ᵀ * minkowskiMetric *
          (principalOrientationReflection4 *
            (actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹) =
        ((actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹)ᵀ *
          (principalOrientationReflection4ᵀ * minkowskiMetric *
            principalOrientationReflection4) *
          (actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹ := by
            noncomm_ring
      _ = coordinateMetricMatrixField4 g z := by
        rw [principalOrientationReflection4_metric]
        exact hbase

@[simp] theorem actualMetricPrincipalFrameCandidateField4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool) :
    actualMetricPrincipalFrameCandidateField4 g
        (choice.withOrientationReverse reverse) =
      actualMetricPrincipalFrameCandidateField4 g choice := by
  rfl

theorem actualMetricPrincipalCoframeCandidateField4_orientation_true
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse true) =
      fun z => principalOrientationReflection4 *
        actualMetricPrincipalCoframeCandidateField4 g
          (choice.withOrientationReverse false) z := by
  funext z
  simp [actualMetricPrincipalCoframeCandidateField4,
    orientPrincipalCoframe4]

theorem actualMetricPrincipalCoframeCandidateField4_det_orientation_true
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) :
    Matrix.det (actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse true) z) =
      -Matrix.det (actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse false) z) := by
  rw [congrFun
    (actualMetricPrincipalCoframeCandidateField4_orientation_true g choice) z,
    Matrix.det_mul, principalOrientationReflection4_det]
  ring

/-- Every nondegenerate selected tetrad has exactly one of the two finite
orientation branches positively oriented relative to the coordinate chart. -/
theorem exists_actualMetricPositiveOrientationChoice
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hdet : Matrix.det (actualMetricPrincipalCoframeCandidateField4 g
      (choice.withOrientationReverse false) z) ≠ 0) :
    ∃ reverse : Bool,
      0 < Matrix.det (actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse reverse) z) := by
  by_cases hpos : 0 < Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse false) z)
  · exact ⟨false, hpos⟩
  · refine ⟨true, ?_⟩
    rw [actualMetricPrincipalCoframeCandidateField4_det_orientation_true]
    have hneg : Matrix.det (actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse false) z) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hdet
    linarith

/-- Channel quotient indices do not affect the constructed principal
coframe. -/
@[simp] theorem actualMetricPrincipalCoframeCandidateField4_withChannel
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (channel : FourthOrderComponentChoice) :
    actualMetricPrincipalCoframeCandidateField4 g
        (choice.withChannel channel) =
      actualMetricPrincipalCoframeCandidateField4 g choice := by
  rfl

/-- Full Ricci reconstruction obstruction for one completely metric-derived
scalar choice. -/
noncomputable def actualMetricReconstructionObstruction4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  let R := actualMixedRicciField4 g z
  let V := actualMetricScalarContributionCandidateField4 g choice z
  let traceV := scalarContributionTraceField
    (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus) z
  R * V + V * R - traceV • V -
    (R * R - actualRicciReconstructedQSqField4 g z • (1 : Matrix4))

/-- Algebraic entrance conditions for the completely metric-only detector.
Besides the coefficient obstruction, these conditions directly test the
simple real four-root branch and certify that the two complementary
polynomial projectors are genuine rank-one eigenspace projectors.  Thus the
known coefficient-level false positives cannot enter the accepted set. -/
def IsActualMetricAlgebraicEntranceAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  let G := coordinateMetricMatrixField4 g z
  let R := actualMixedRicciField4 g z
  let d := actualRicciCharacteristicDataField4 g z
  let qSq := actualRicciReconstructedQSqField4 g z
  let q := actualRicciProtectedRootField4 g z
  let a := actualRicciComplementaryRootAField4 g z
  let b := actualRicciComplementaryRootBField4 g z
  let PA := actualRicciComplementaryProjectorAField4 g z
  let PB := actualRicciComplementaryProjectorBField4 g z
  G.transpose = G ∧
  Matrix.det G < 0 ∧
  G * G⁻¹ = 1 ∧
  (G * R).transpose = G * R ∧
  d.e1 ≠ 0 ∧
  kaluzaObstruction d = 0 ∧
  0 < qSq ∧
  0 < actualRicciComplementaryDiscriminantField4 g z ∧
  a ≠ -q ∧ a ≠ b ∧ a ≠ q ∧
  -q ≠ b ∧ -q ≠ q ∧ b ≠ q ∧
  PA * PA = PA ∧ PB * PB = PB ∧ PA * PB = 0 ∧
  Matrix.trace PA = 1 ∧ Matrix.trace PB = 1 ∧
  R * PA = a • PA ∧ R * PB = b • PB

/-- The algebraic entrance's directly testable idempotence and trace-one
conditions really do certify rank-one ranges for both scalar projectors. -/
theorem IsActualMetricAlgebraicEntranceAt4.scalarProjectorRanks
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (h : IsActualMetricAlgebraicEntranceAt4 g z) :
    Module.finrank ℝ
        (Matrix.toLin' (actualRicciComplementaryProjectorAField4 g z)).range = 1 ∧
      Module.finrank ℝ
        (Matrix.toLin' (actualRicciComplementaryProjectorBField4 g z)).range = 1 := by
  unfold IsActualMetricAlgebraicEntranceAt4 at h
  dsimp only at h
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hPAidem, hPBidem, _, htraceA, htraceB, _⟩
  exact ⟨
    matrixProjector_finrank_range_eq_one_of_trace_one
      (actualRicciComplementaryProjectorAField4 g z) hPAidem htraceA,
    matrixProjector_finrank_range_eq_one_of_trace_one
      (actualRicciComplementaryProjectorBField4 g z) hPBidem htraceB⟩

/-- Choice-independent causal labeling of the two scalar Ricci eigenlines.
Every nonzero vector in the lower-root range is timelike and every nonzero
vector in the upper-root range is spacelike.  Unlike a fixed-probe sign test,
this statement names no detector choice and is invariant under rescaling or
reorientation of either line. -/
def IsActualMetricScalarEigenlineCausalAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  let PA := actualRicciComplementaryProjectorAField4 g z
  let PB := actualRicciComplementaryProjectorBField4 g z
  (∀ x : (Matrix.toLin' PA).range,
      (x : CurvatureCoordinateSpace4) ≠ 0 →
      continuousBilinFormToBilin (g z)
        (x : CurvatureCoordinateSpace4) (x : CurvatureCoordinateSpace4) < 0) ∧
    (∀ x : (Matrix.toLin' PB).range,
      (x : CurvatureCoordinateSpace4) ≠ 0 →
      0 < continuousBilinFormToBilin (g z)
        (x : CurvatureCoordinateSpace4) (x : CurvatureCoordinateSpace4))

/-- **Actual-metric finite scalar-probe existence.** The directly checked
idempotence/trace-one projector identities and intrinsic causal labeling force
the detector's finite coordinate search to contain an admissible probe for
each scalar eigenline.  Both strict signs persist locally.  Thus scalar probe
indices are outputs of finite search, not geometric entrance data. -/
theorem exists_eventually_actualMetricScalarProbeChoice
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hPA : ∀ a b, ContinuousAt
      (fun w => actualRicciComplementaryProjectorAField4 g w a b) z)
    (hPB : ∀ a b, ContinuousAt
      (fun w => actualRicciComplementaryProjectorBField4 g w a b) z)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (hcausal : IsActualMetricScalarEigenlineCausalAt4 g z) :
    ∃ i j : Fin 4,
      let selected := choice.withScalarProbes i j
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g
            (smoothMatrixProjectedVector
              (actualRicciComplementaryProjectorAField4 g)
              (curvatureCoordinateDirection selected.scalarTimelikeProbe))
            (smoothMatrixProjectedVector
              (actualRicciComplementaryProjectorAField4 g)
              (curvatureCoordinateDirection selected.scalarTimelikeProbe)) w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMatrixProjectedVector
              (actualRicciComplementaryProjectorBField4 g)
              (curvatureCoordinateDirection selected.scalarSpacelikeProbe))
            (smoothMatrixProjectedVector
              (actualRicciComplementaryProjectorBField4 g)
              (curvatureCoordinateDirection selected.scalarSpacelikeProbe)) w := by
  unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic
  dsimp only at halgebraic
  rcases halgebraic with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hPAidem, hPBidem, _, htraceA, htraceB, _⟩
  unfold IsActualMetricScalarEigenlineCausalAt4 at hcausal
  dsimp only at hcausal
  obtain ⟨i, j, hlocal⟩ :=
    exists_eventually_smoothMatrixProjectedBasisScalarEigenlineSignsAt
      g (actualRicciComplementaryProjectorAField4 g)
      (actualRicciComplementaryProjectorBField4 g) z hg hPA hPB
      hPAidem hPBidem htraceA htraceB hcausal.1 hcausal.2
  refine ⟨i, j, ?_⟩
  simpa only [ActualMetricDetectorChoice4.withScalarProbes_timelike,
    ActualMetricDetectorChoice4.withScalarProbes_spacelike] using hlocal

/-- Algebraic certification of the Maxwell residual and its two principal
planes for one raw scalar choice.  These equalities are retained as explicit
finite tests at the metric-only boundary, even though the square and
projector laws can later be derived from the reconstruction equation. -/
def IsActualMetricMaxwellEntranceAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  let G := coordinateMetricMatrixField4 g z
  let qSq := actualRicciReconstructedQSqField4 g z
  let S := actualMetricMaxwellResidualCandidateField4 g choice z
  let P := actualMetricMaxwellMinusProjectorCandidateField4 g choice z
  let Q := actualMetricMaxwellPlusProjectorCandidateField4 g choice z
  S * S = qSq • (1 : Matrix4) ∧
  (G * S).transpose = G * S ∧
  P * P = P ∧ Q * Q = Q ∧ P * Q = 0 ∧ P + Q = 1

@[simp] theorem isActualMetricMaxwellEntranceAt4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool)
    (z : CurvatureCoordinateSpace4) :
    IsActualMetricMaxwellEntranceAt4 g
        (choice.withOrientationReverse reverse) z ↔
      IsActualMetricMaxwellEntranceAt4 g choice z := by
  rfl

/-- The complete sign-tested actual-metric tetrad is genuinely
pseudo-orthonormal, including when its timelike pivot is a metric-dependent
finite combination of two projected coordinate vectors. -/
theorem actualMetricPrincipalTetradCandidate_pseudoOrthonormal
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hqSqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z)
    (hx : smoothMetricPairing g
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) z)
    (hu : 0 < smoothMetricPairing g
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g choice) z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice)) z) :
    IsPseudoOrthonormalPrincipalTetrad
      (continuousBilinFormToBilin (g z))
      (actualMetricPrincipalTetradCandidateField4 g choice z).1
      (actualMetricPrincipalTetradCandidateField4 g choice z).2 := by
  unfold IsActualMetricMaxwellEntranceAt4 at hmaxwell
  dsimp only at hmaxwell
  rcases hmaxwell with ⟨hSq, hselfMatrix, hP, hQ, hPQ, _⟩
  let P := actualMetricMaxwellMinusProjectorCandidateField4 g choice z
  let Q := actualMetricMaxwellPlusProjectorCandidateField4 g choice z
  let Plin := Matrix.toLin' P
  let Qlin := Matrix.toLin' Q
  have hPcomp : Plin.comp Plin = Plin := by
    have h' := congrArg Matrix.toLin' hP
    rw [Matrix.toLin'_mul] at h'
    exact h'
  have hQcomp : Qlin.comp Qlin = Qlin := by
    have h' := congrArg Matrix.toLin' hQ
    rw [Matrix.toLin'_mul] at h'
    exact h'
  have hminus0 : Plin
      (actualMetricMaxwellMinusProbe0Field4 g choice z) =
      actualMetricMaxwellMinusProbe0Field4 g choice z := by
    exact projector_apply_fixed Plin hPcomp
      (curvatureCoordinateDirection choice.maxwellMinusProbe0)
  have hminus1 : Plin
      (actualMetricMaxwellMinusProbe1Field4 g choice z) =
      actualMetricMaxwellMinusProbe1Field4 g choice z := by
    exact projector_apply_fixed Plin hPcomp
      (curvatureCoordinateDirection choice.maxwellMinusProbe1)
  have hminus0Matrix : P *ᵥ
      actualMetricMaxwellMinusProbe0Field4 g choice z =
      actualMetricMaxwellMinusProbe0Field4 g choice z := by
    simpa [Plin, Matrix.toLin'_apply] using hminus0
  have hminus1Matrix : P *ᵥ
      actualMetricMaxwellMinusProbe1Field4 g choice z =
      actualMetricMaxwellMinusProbe1Field4 g choice z := by
    simpa [Plin, Matrix.toLin'_apply] using hminus1
  have hpivot : Plin
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice z) =
      actualMetricMaxwellLorentzPivotCandidateField4 g choice z := by
    cases hrecipe : choice.maxwellMinusPivotRecipe <;>
      simp [actualMetricMaxwellLorentzPivotCandidateField4,
        smoothLorentzianPivotCandidate, hrecipe,
        Plin, Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_sub,
        Matrix.mulVec_smul, hminus0Matrix, hminus1Matrix]
  have hcompanion : Plin
      (actualMetricMaxwellLorentzCompanionCandidateField4 g choice z) =
      actualMetricMaxwellLorentzCompanionCandidateField4 g choice z := by
    cases hrecipe : choice.maxwellMinusPivotRecipe <;>
      simp [actualMetricMaxwellLorentzCompanionCandidateField4,
        smoothLorentzianPivotCompanion, hrecipe,
        Plin, Matrix.toLin'_apply, hminus0Matrix, hminus1Matrix]
  have hplus0 : Qlin
      (actualMetricMaxwellPlusProbe0Field4 g choice z) =
      actualMetricMaxwellPlusProbe0Field4 g choice z := by
    exact projector_apply_fixed Qlin hQcomp
      (curvatureCoordinateDirection choice.maxwellPlusProbe0)
  have hplus1 : Qlin
      (actualMetricMaxwellPlusProbe1Field4 g choice z) =
      actualMetricMaxwellPlusProbe1Field4 g choice z := by
    exact projector_apply_fixed Qlin hQcomp
      (curvatureCoordinateDirection choice.maxwellPlusProbe1)
  have hGsym := coordinateMetricMatrixField4_transpose_eq_self g z hgsymm
  have hself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin'
        (actualMetricMaxwellResidualCandidateField4 g choice z)) := by
    have hs := matrixMetricSelfAdjoint_of_mul_transpose_eq
      (coordinateMetricMatrixField4 g z)
      (actualMetricMaxwellResidualCandidateField4 g choice z)
      hGsym hselfMatrix
    rwa [coordinateMetricMatrixField4_toBilin' g z] at hs
  apply smoothCurvatureMaxwellPrincipalTetradFromFields_pseudoOrthonormal
    g (actualMetricMaxwellResidualCandidateField4 g choice)
    (actualRicciReconstructedQSqField4 g)
    (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
    (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)
    (actualMetricMaxwellPlusProbe0Field4 g choice)
    (actualMetricMaxwellPlusProbe1Field4 g choice)
    z hgsymm hSq hself hqSqPos
  · exact hpivot
  · exact hcompanion
  · exact hplus0
  · exact hplus1
  · exact hx
  · exact hy
  · exact hu
  · exact hv

/-- **Arbitrary-chart coframe correctness from the detector gates.** Maxwell
algebra plus the four explicit frame signs force the selected true dual
coframe to reconstruct the actual coordinate metric exactly.  No preferred
orthonormal chart is assumed. -/
theorem actualMetricPrincipalCoframeCandidate_metric_of_maxwellEntrance
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hqSqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z)
    (hx : smoothMetricPairing g
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) z)
    (hu : 0 < smoothMetricPairing g
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g choice) z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice)) z) :
    (actualMetricPrincipalCoframeCandidateField4 g choice z)ᵀ *
        minkowskiMetric *
        actualMetricPrincipalCoframeCandidateField4 g choice z =
      coordinateMetricMatrixField4 g z := by
  apply actualMetricPrincipalCoframeCandidate_metric g choice z hgsymm
  exact actualMetricPrincipalTetradCandidate_pseudoOrthonormal
    g choice z hgsymm hqSqPos hmaxwell hx hy hu hv

/-- Maxwell entrance and frame signs also construct a positively oriented
finite coframe choice in an arbitrary Lorentzian coordinate chart. -/
theorem exists_actualMetricPositiveOrientationChoice_of_maxwellEntrance
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hdetG : Matrix.det (coordinateMetricMatrixField4 g z) < 0)
    (hqSqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z)
    (hx : smoothMetricPairing g
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) z)
    (hu : 0 < smoothMetricPairing g
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g choice) z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice)) z) :
    ∃ reverse : Bool,
      0 < Matrix.det (actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse reverse) z) := by
  let base := choice.withOrientationReverse false
  have hmetric :=
    actualMetricPrincipalCoframeCandidate_metric_of_maxwellEntrance
      g base z hgsymm hqSqPos
      (by simpa [base]
        using hmaxwell)
      (by simpa [base]
        using hx)
      (by simpa [base]
        using hy)
      (by simpa [base]
        using hu)
      (by simpa [base]
        using hv)
  have hdet : Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g base z) ≠ 0 := by
    intro hzero
    have hd := congrArg Matrix.det hmetric
    simp [Matrix.det_mul, hzero] at hd
    rw [← hd] at hdetG
    linarith
  exact exists_actualMetricPositiveOrientationChoice g choice z
    (by simpa [base] using hdet)

/-- **Actual-detector Lorentzian frame selection from positive energy.** Fix
only a scalar branch.  If its metric-derived residual passes the Maxwell
square/self-adjoint tests, is tracefree, and has positive observer energy,
then the finite detector contains a replacement negative-plane coordinate
pair and pivot recipe whose two strict signs persist locally.  No preferred
frame is supplied in the hypotheses. -/
theorem exists_eventually_actualMetricMaxwellMinusFrameChoice_of_positiveEnergy
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hP : ∀ a b, ContinuousAt
      (fun w => actualMetricMaxwellMinusProjectorCandidateField4
        g choice w a b) z)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (htrace : Matrix.trace
      (actualMetricMaxwellResidualCandidateField4 g choice z) = 0)
    (henergy : HasPositiveMaxwellEnergyDensity
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin'
        (actualMetricMaxwellResidualCandidateField4 g choice z)))
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe,
      let selected := choice.withMaxwellMinusFrame i j recipe
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g
            (actualMetricMaxwellLorentzPivotCandidateField4 g selected)
            (actualMetricMaxwellLorentzPivotCandidateField4 g selected) w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellLorentzPivotCandidateField4 g selected)
              (actualMetricMaxwellLorentzCompanionCandidateField4 g selected))
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellLorentzPivotCandidateField4 g selected)
              (actualMetricMaxwellLorentzCompanionCandidateField4 g selected)) w := by
  unfold IsActualMetricMaxwellEntranceAt4 at hmaxwell
  dsimp only at hmaxwell
  rcases hmaxwell with ⟨hSq, hselfMatrix, _⟩
  have hGsym :=
    coordinateMetricMatrixField4_transpose_eq_self g z hgsymm
  have hself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin'
        (actualMetricMaxwellResidualCandidateField4 g choice z)) := by
    have h := matrixMetricSelfAdjoint_of_mul_transpose_eq
      (coordinateMetricMatrixField4 g z)
      (actualMetricMaxwellResidualCandidateField4 g choice z)
      hGsym hselfMatrix
    rwa [coordinateMetricMatrixField4_toBilin' g z] at h
  obtain ⟨i, j, recipe, hlocal⟩ :=
    exists_eventually_smoothMatrixProjectedMaxwellLorentzianFrameSignsAt_of_positiveEnergy
      g (actualMetricMaxwellResidualCandidateField4 g choice)
      (actualRicciReconstructedQSqField4 g) z hg hP hgsymm hindex
      hqPos hSq htrace hself henergy
  refine ⟨i, j, recipe, ?_⟩
  simpa only [
    actualMetricMaxwellLorentzPivotCandidateField4,
    actualMetricMaxwellLorentzCompanionCandidateField4,
    actualMetricMaxwellMinusProbe0Field4,
    actualMetricMaxwellMinusProbe1Field4,
    ActualMetricDetectorChoice4.withMaxwellMinusFrame_probe0,
    ActualMetricDetectorChoice4.withMaxwellMinusFrame_probe1,
    ActualMetricDetectorChoice4.withMaxwellMinusFrame_recipe,
    actualMetricMaxwellMinusProjectorCandidateField4_withMaxwellMinusFrame,
    actualMetricMaxwellMinusProjectorCandidateField4,
    actualMetricMaxwellResidualCandidateField4_withMaxwellMinusFrame] using hlocal

/-- **Actual-detector complete Maxwell frame selection from positive
energy.** Fixing only the scalar branch, the metric-derived Maxwell tests and
positive observer energy force a finite replacement of all Maxwell frame
indices whose four strict principal-frame signs persist on a neighborhood. -/
theorem exists_eventually_actualMetricMaxwellFrameChoice_of_positiveEnergy
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hP : ∀ a b, ContinuousAt
      (fun w => actualMetricMaxwellMinusProjectorCandidateField4
        g choice w a b) z)
    (hQ : ∀ a b, ContinuousAt
      (fun w => actualMetricMaxwellPlusProjectorCandidateField4
        g choice w a b) z)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (htrace : Matrix.trace
      (actualMetricMaxwellResidualCandidateField4 g choice z) = 0)
    (henergy : HasPositiveMaxwellEnergyDensity
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin'
        (actualMetricMaxwellResidualCandidateField4 g choice z)))
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe, ∃ k l : Fin 4,
      let selected := choice.withMaxwellFrame i j recipe k l
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g
            (actualMetricMaxwellLorentzPivotCandidateField4 g selected)
            (actualMetricMaxwellLorentzPivotCandidateField4 g selected) w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellLorentzPivotCandidateField4 g selected)
              (actualMetricMaxwellLorentzCompanionCandidateField4 g selected))
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellLorentzPivotCandidateField4 g selected)
              (actualMetricMaxwellLorentzCompanionCandidateField4 g selected)) w ∧
          0 < smoothMetricPairing g
            (actualMetricMaxwellPlusProbe0Field4 g selected)
            (actualMetricMaxwellPlusProbe0Field4 g selected) w ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellPlusProbe0Field4 g selected)
              (actualMetricMaxwellPlusProbe1Field4 g selected))
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellPlusProbe0Field4 g selected)
              (actualMetricMaxwellPlusProbe1Field4 g selected)) w := by
  unfold IsActualMetricMaxwellEntranceAt4 at hmaxwell
  dsimp only at hmaxwell
  rcases hmaxwell with ⟨hSq, hselfMatrix, _⟩
  have hGsym :=
    coordinateMetricMatrixField4_transpose_eq_self g z hgsymm
  have hself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin'
        (actualMetricMaxwellResidualCandidateField4 g choice z)) := by
    have h := matrixMetricSelfAdjoint_of_mul_transpose_eq
      (coordinateMetricMatrixField4 g z)
      (actualMetricMaxwellResidualCandidateField4 g choice z)
      hGsym hselfMatrix
    rwa [coordinateMetricMatrixField4_toBilin' g z] at h
  obtain ⟨i, j, recipe, k, l, hlocal⟩ :=
    exists_eventually_smoothMatrixProjectedMaxwellPrincipalFrameSignsAt_of_positiveEnergy
      g (actualMetricMaxwellResidualCandidateField4 g choice)
      (actualRicciReconstructedQSqField4 g) z hg hP hQ hgsymm hindex
      hqPos hSq htrace hself henergy
  refine ⟨i, j, recipe, k, l, ?_⟩
  simpa only [
    actualMetricMaxwellLorentzPivotCandidateField4,
    actualMetricMaxwellLorentzCompanionCandidateField4,
    actualMetricMaxwellMinusProbe0Field4,
    actualMetricMaxwellMinusProbe1Field4,
    actualMetricMaxwellPlusProbe0Field4,
    actualMetricMaxwellPlusProbe1Field4,
    ActualMetricDetectorChoice4.withMaxwellFrame_probe0,
    ActualMetricDetectorChoice4.withMaxwellFrame_probe1,
    ActualMetricDetectorChoice4.withMaxwellFrame_recipe,
    ActualMetricDetectorChoice4.withMaxwellFrame_plusProbe0,
    ActualMetricDetectorChoice4.withMaxwellFrame_plusProbe1,
    actualMetricMaxwellMinusProjectorCandidateField4_withMaxwellFrame,
    actualMetricMaxwellPlusProjectorCandidateField4_withMaxwellFrame,
    actualMetricMaxwellMinusProjectorCandidateField4,
    actualMetricMaxwellPlusProjectorCandidateField4,
    actualMetricMaxwellResidualCandidateField4_withMaxwellFrame] using hlocal

/-- Electric curvature seed selected by one finite actual-metric choice. -/
noncomputable def actualMetricElectricSeedCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → Matrix4 := fun z =>
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  transportTwoForm L
    (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)

/-- Actual coordinate-metric Hodge star of the selected electric seed. -/
noncomputable def actualMetricHodgeElectricSeedCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → Matrix4 := fun z =>
  coordinateMetricHodgeTwoForm4 (coordinateMetricMatrixField4 g z)
    (actualMetricElectricSeedCandidateField4 g choice z)

/-- Canonical Hodge partner transported by the selected principal coframe. -/
noncomputable def actualMetricTransportedHodgeSeedCandidateField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureCoordinateSpace4 → Matrix4 := fun z =>
  transportedPositiveQHodgeSeed
    (actualMetricPrincipalCoframeCandidateField4 g choice z)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) z)

/-- Reversing the finite orientation bit leaves the canonical electric seed
unchanged. -/
theorem actualMetricElectricSeedCandidateField4_orientation_true
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    actualMetricElectricSeedCandidateField4 g
        (choice.withOrientationReverse true) =
      actualMetricElectricSeedCandidateField4 g
        (choice.withOrientationReverse false) := by
  funext z
  unfold actualMetricElectricSeedCandidateField4
  rw [actualMetricPrincipalCoframeCandidateField4_orientation_true]
  rw [transportTwoForm_mul,
    principalOrientationReflection4_electric]

/-- The same finite orientation reversal negates the transported canonical
Hodge partner. -/
theorem actualMetricTransportedHodgeSeedCandidateField4_orientation_true
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    actualMetricTransportedHodgeSeedCandidateField4 g
        (choice.withOrientationReverse true) =
      fun z => -actualMetricTransportedHodgeSeedCandidateField4 g
        (choice.withOrientationReverse false) z := by
  funext z
  unfold actualMetricTransportedHodgeSeedCandidateField4
    transportedPositiveQHodgeSeed
  rw [actualMetricPrincipalCoframeCandidateField4_orientation_true]
  rw [transportTwoForm_mul,
    principalOrientationReflection4_hodge]
  simpa only [neg_smul, one_smul] using transportTwoForm_smul
      (actualMetricPrincipalCoframeCandidateField4 g
        (choice.withOrientationReverse false) z)
      (canonicalHodgeStar
        (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z)) 0) (-1)

/-- The metric Hodge star of the electric seed is orientation-bit
independent because the electric seed itself is. -/
theorem actualMetricHodgeElectricSeedCandidateField4_orientation_true
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    actualMetricHodgeElectricSeedCandidateField4 g
        (choice.withOrientationReverse true) =
      actualMetricHodgeElectricSeedCandidateField4 g
        (choice.withOrientationReverse false) := by
  unfold actualMetricHodgeElectricSeedCandidateField4
  rw [actualMetricElectricSeedCandidateField4_orientation_true]

/-- The canonical partner transported by a raw principal coframe must be the
actual coordinate-metric Hodge star of the transported electric seed.  This
finite equality fixes the orientation branch and prevents the detector's
second exterior channel from being an independently supplied convention. -/
def IsActualMetricHodgeCompatibleAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  actualMetricHodgeElectricSeedCandidateField4 g choice z =
    actualMetricTransportedHodgeSeedCandidateField4 g choice z

/-- Choice-independent Hodge naturality boundary.  A pseudo-orthonormal
coframe determines the canonical Hodge partner up to exactly the two
spacetime orientations; no detector orientation bit occurs in this
predicate. -/
def IsActualMetricHodgeCompatibleUpToOrientationAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  let base := choice.withOrientationReverse false
  actualMetricHodgeElectricSeedCandidateField4 g base z =
      actualMetricTransportedHodgeSeedCandidateField4 g base z ∨
    actualMetricHodgeElectricSeedCandidateField4 g base z =
      -actualMetricTransportedHodgeSeedCandidateField4 g base z

/-- **Exact actual-metric Hodge naturality for a positive coframe.** Once the
selected principal coframe reconstructs the coordinate metric and has positive
determinant, orientation-preserving coordinate Hodge naturality identifies the
transported canonical partner with the actual metric Hodge star exactly. -/
theorem isActualMetricHodgeCompatibleAt4_of_coframeMetric_det_pos
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hmetric :
      let L := actualMetricPrincipalCoframeCandidateField4 g choice z
      Lᵀ * minkowskiMetric * L = coordinateMetricMatrixField4 g z)
    (hdet : 0 < Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g choice z)) :
    IsActualMetricHodgeCompatibleAt4 g choice z := by
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  have hunit : IsUnit (Matrix.det L) := isUnit_iff_ne_zero.mpr (by
    exact ne_of_gt (by simpa [L] using hdet))
  have hKL : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hunit
  have hLK : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hunit
  have hnatural := coordinateMetricHodgeTwoForm4_canonical_of_det_pos
    (coordinateMetricMatrixField4 g z) L L⁻¹
    (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) z)) 0
    (by simpa [L] using hmetric.symm) hKL hLK
    (by simpa [L] using hdet)
  unfold IsActualMetricHodgeCompatibleAt4
  simpa [L, actualMetricHodgeElectricSeedCandidateField4,
    actualMetricElectricSeedCandidateField4,
    actualMetricTransportedHodgeSeedCandidateField4,
    transportedPositiveQHodgeSeed] using hnatural

/-- **Actual-metric Hodge naturality from coframe geometry.** Once the raw
principal coframe reconstructs the coordinate metric and is nondegenerate,
the explicit coordinate Hodge formula agrees with its transported canonical
partner up to exactly the two orientation signs. -/
theorem isActualMetricHodgeCompatibleUpToOrientationAt4_of_coframeMetric
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hmetric :
      let base := choice.withOrientationReverse false
      let L := actualMetricPrincipalCoframeCandidateField4 g base z
      Lᵀ * minkowskiMetric * L = coordinateMetricMatrixField4 g z)
    (hdet :
      let base := choice.withOrientationReverse false
      Matrix.det
        (actualMetricPrincipalCoframeCandidateField4 g base z) ≠ 0) :
    IsActualMetricHodgeCompatibleUpToOrientationAt4 g choice z := by
  let base := choice.withOrientationReverse false
  let L := actualMetricPrincipalCoframeCandidateField4 g base z
  have hunit : IsUnit (Matrix.det L) := isUnit_iff_ne_zero.mpr (by
    simpa [base, L] using hdet)
  have hKL : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hunit
  have hLK : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hunit
  have hnatural :=
    coordinateMetricHodgeTwoForm4_canonical_up_to_orientation
      (coordinateMetricMatrixField4 g z) L L⁻¹
      (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z)) 0
      (by simpa [base, L] using hmetric.symm) hKL hLK
  unfold IsActualMetricHodgeCompatibleUpToOrientationAt4
  dsimp only
  simpa [base, L, actualMetricHodgeElectricSeedCandidateField4,
    actualMetricElectricSeedCandidateField4,
    actualMetricTransportedHodgeSeedCandidateField4,
    transportedPositiveQHodgeSeed] using hnatural

/-- The actual detector's Maxwell/frame gates discharge Hodge naturality;
it is no longer an independent physical entrance hypothesis. -/
theorem isActualMetricHodgeCompatibleUpToOrientationAt4_of_maxwellEntrance
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hdetG : Matrix.det (coordinateMetricMatrixField4 g z) < 0)
    (hqSqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z)
    (hx : smoothMetricPairing g
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) z)
    (hu : 0 < smoothMetricPairing g
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g choice) z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice)) z) :
    IsActualMetricHodgeCompatibleUpToOrientationAt4 g choice z := by
  let base := choice.withOrientationReverse false
  have hmetric :=
    actualMetricPrincipalCoframeCandidate_metric_of_maxwellEntrance
      g base z hgsymm hqSqPos
      (by simpa [base] using hmaxwell)
      (by simpa [base] using hx)
      (by simpa [base] using hy)
      (by simpa [base] using hu)
      (by simpa [base] using hv)
  have hdet : Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g base z) ≠ 0 := by
    intro hzero
    have hd := congrArg Matrix.det hmetric
    simp [Matrix.det_mul, hzero, minkowskiMetric_det] at hd
    linarith
  apply isActualMetricHodgeCompatibleUpToOrientationAt4_of_coframeMetric
    g choice z
  · simpa [base] using hmetric
  · simpa [base] using hdet

/-- The Maxwell/frame entrance gates plus positive orientation of the selected
coframe discharge the detector's exact Hodge-compatibility gate without a
separate Hodge sign selection. -/
theorem isActualMetricHodgeCompatibleAt4_of_maxwellEntrance_det_pos
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hqSqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z)
    (hx : smoothMetricPairing g
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) z)
    (hu : 0 < smoothMetricPairing g
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g choice) z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice)) z)
    (hdet : 0 < Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g choice z)) :
    IsActualMetricHodgeCompatibleAt4 g choice z := by
  apply isActualMetricHodgeCompatibleAt4_of_coframeMetric_det_pos
    g choice z
  · exact actualMetricPrincipalCoframeCandidate_metric_of_maxwellEntrance
      g choice z hgsymm hqSqPos hmaxwell hx hy hu hv
  · exact hdet

/-- **Finite Hodge-orientation selection.** Once metric Hodge naturality is
known up to orientation, one of the two explicitly enumerated orientation
bits passes the detector's exact Hodge equality. -/
theorem exists_actualMetricHodgeOrientationChoice
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (h : IsActualMetricHodgeCompatibleUpToOrientationAt4 g choice z) :
    ∃ reverse : Bool,
      IsActualMetricHodgeCompatibleAt4 g
        (choice.withOrientationReverse reverse) z := by
  unfold IsActualMetricHodgeCompatibleUpToOrientationAt4 at h
  dsimp only at h
  rcases h with hplus | hminus
  · exact ⟨false, hplus⟩
  · refine ⟨true, ?_⟩
    unfold IsActualMetricHodgeCompatibleAt4
    rw [actualMetricHodgeElectricSeedCandidateField4_orientation_true,
      actualMetricTransportedHodgeSeedCandidateField4_orientation_true]
    exact hminus

/-- **Finite Hodge branch existence from the metric gates alone.** The
Lorentzian algebraic gate, Maxwell entrance, and four frame signs force one
of the detector's two orientation bits to pass the exact coordinate Hodge
equality. -/
theorem exists_actualMetricHodgeOrientationChoice_of_maxwellEntrance
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hdetG : Matrix.det (coordinateMetricMatrixField4 g z) < 0)
    (hqSqPos : 0 < actualRicciReconstructedQSqField4 g z)
    (hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice z)
    (hx : smoothMetricPairing g
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) z)
    (hu : 0 < smoothMetricPairing g
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g choice) z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice)) z) :
    ∃ reverse : Bool,
      IsActualMetricHodgeCompatibleAt4 g
        (choice.withOrientationReverse reverse) z := by
  apply exists_actualMetricHodgeOrientationChoice g choice z
  exact
    isActualMetricHodgeCompatibleUpToOrientationAt4_of_maxwellEntrance
      g choice z hgsymm hdetG hqSqPos hmaxwell hx hy hu hv

/-- Conversely, either accepted finite orientation is precisely an
orientation-free up-to-sign Hodge certificate. -/
theorem hodgeCompatibleUpToOrientation_of_orientationChoice
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (reverse : Bool)
    (h : IsActualMetricHodgeCompatibleAt4 g
      (choice.withOrientationReverse reverse) z) :
    IsActualMetricHodgeCompatibleUpToOrientationAt4 g choice z := by
  cases reverse
  · exact Or.inl h
  · right
    unfold IsActualMetricHodgeCompatibleAt4 at h
    rw [actualMetricHodgeElectricSeedCandidateField4_orientation_true,
      actualMetricTransportedHodgeSeedCandidateField4_orientation_true] at h
    exact h

/-- Upstream algebraic/scalar/frame/Hodge entrance for one finite raw metric
choice, before the fourth-order channel test.  Isolating this predicate makes
the live necessity boundary explicit: genuine EMD closure will construct the
channel acceptance, while these are the finite metric-only entrance tests
whose probe existence must still be supplied on the stated chart branch. -/
def IsActualMetricUpstreamEntranceAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) : Prop :=
  let a := actualRicciComplementaryRootAField4 g
  let b := actualRicciComplementaryRootBField4 g
  let qSq := actualRicciReconstructedQSqField4 g
  let PA := actualRicciComplementaryProjectorAField4 g
  let PB := actualRicciComplementaryProjectorBField4 g
  let u0 := actualMetricMaxwellLorentzPivotCandidateField4 g choice
  let u1 := actualMetricMaxwellLorentzCompanionCandidateField4 g choice
  let v0 := actualMetricMaxwellPlusProbe0Field4 g choice
  let v1 := actualMetricMaxwellPlusProbe1Field4 g choice
  IsActualMetricAlgebraicEntranceAt4 g z ∧
  0 < 2 * (-1 : ℝ) * reconstructedDiagonalAField a b qSq z ∧
  0 < 2 * (1 : ℝ) * reconstructedDiagonalBField a b qSq z ∧
  smoothMetricPairing g
      (smoothMatrixProjectedVector PA
        (curvatureCoordinateDirection choice.scalarTimelikeProbe))
      (smoothMatrixProjectedVector PA
        (curvatureCoordinateDirection choice.scalarTimelikeProbe)) z < 0 ∧
  0 < smoothMetricPairing g
      (smoothMatrixProjectedVector PB
        (curvatureCoordinateDirection choice.scalarSpacelikeProbe))
      (smoothMatrixProjectedVector PB
        (curvatureCoordinateDirection choice.scalarSpacelikeProbe)) z ∧
  actualMetricScalarClosureObstruction4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z = 0 ∧
  actualMetricReconstructionObstruction4 g choice z = 0 ∧
  IsActualMetricMaxwellEntranceAt4 g choice z ∧
  IsActualMetricHodgeCompatibleAt4 g choice z ∧
  smoothMetricPairing g u0 u0 z < 0 ∧
  0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g u0 u1)
      (smoothMetricOrthogonalizeSecond g u0 u1) z ∧
  0 < smoothMetricPairing g v0 v0 z ∧
  0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g v0 v1)
      (smoothMetricOrthogonalizeSecond g v0 v1) z

/-- **Completely metric-only fourth-order acceptance predicate.** Every
quantity is a formula in the actual metric and its finite derivatives.  The
finite choice merely selects coordinate-basis probes, a relative-sign scalar
branch, and quotient components.  Acceptance is exactly the upstream
metric-only entrance plus the complete channel/next-order obstruction. -/
def IsActualMetricFourthOrderDetectorCandidateAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) : Prop :=
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let qSq := actualRicciReconstructedQSqField4 g
  let scalarV := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus
  IsActualMetricUpstreamEntranceAt4 g z choice ∧
  IsCurvatureSeedFourthOrderCandidateAt L
    (positiveMaxwellMagnitudeFromSquare qSq) scalarV z choice.channel

/-- Channel/source/wedge indices do not affect the upstream metric entrance. -/
@[simp] theorem isActualMetricUpstreamEntranceAt4_withChannel
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (channel : FourthOrderComponentChoice) :
    IsActualMetricUpstreamEntranceAt4 g z
      (choice.withChannel channel) ↔
      IsActualMetricUpstreamEntranceAt4 g z choice := by
  rfl

/-- The upstream algebraic entrance already makes the constructed positive
Maxwell magnitude strictly positive. -/
theorem IsActualMetricUpstreamEntranceAt4.qPos
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (h : IsActualMetricUpstreamEntranceAt4 g z choice) :
    0 < positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) z := by
  have halgebraic := h.1
  unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic
  exact positiveMaxwellMagnitudeFromSquare_pos
    (actualRicciReconstructedQSqField4 g) z
    halgebraic.2.2.2.2.2.2.1

/-- The upstream entrance gates make the selected actual-metric coframe
reconstruct the coordinate metric exactly. -/
theorem actualMetricPrincipalCoframeCandidate_metric_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    (actualMetricPrincipalCoframeCandidateField4 g choice z)ᵀ *
        minkowskiMetric *
        actualMetricPrincipalCoframeCandidateField4 g choice z =
      coordinateMetricMatrixField4 g z := by
  have hup := hupstream
  unfold IsActualMetricUpstreamEntranceAt4 at hup
  dsimp only at hup
  rcases hup with
    ⟨halgebraic, _, _, _, _, _, _, hmaxwell, _, hx, hy, hu, hv⟩
  have halg := halgebraic
  unfold IsActualMetricAlgebraicEntranceAt4 at halg
  dsimp only at halg
  have hGsym : (coordinateMetricMatrixField4 g z)ᵀ =
      coordinateMetricMatrixField4 g z := halg.1
  have hgsymm : (continuousBilinFormToBilin (g z)).IsSymm := by
    have h : (Matrix.toBilin' (coordinateMetricMatrixField4 g z)).IsSymm :=
      Matrix.isSymm_toBilin'_iff_isSymm.mpr hGsym
    simpa [coordinateMetricMatrixField4_toBilin'] using h
  exact actualMetricPrincipalCoframeCandidate_metric_of_maxwellEntrance
    g choice z hgsymm
      halg.2.2.2.2.2.2.1 hmaxwell hx hy hu hv

/-- The upstream-selected actual-metric coframe has nonzero determinant. -/
theorem actualMetricPrincipalCoframeCandidate_det_ne_zero_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    Matrix.det (actualMetricPrincipalCoframeCandidateField4 g choice z) ≠ 0 := by
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  have hmetric :=
    actualMetricPrincipalCoframeCandidate_metric_of_upstream
      g z choice hupstream
  have halgebraic := hupstream.1
  unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic
  dsimp only at halgebraic
  intro hzero
  have hd := congrArg Matrix.det hmetric
  simp [Matrix.det_mul, hzero, minkowskiMetric_det] at hd
  linarith [halgebraic.2.1]

/-- Smoothness of a fixed selected coframe and pointwise upstream entrance
automatically supply the same regularity for its inverse. -/
theorem matrixFieldContDiffOn_actualMetricPrincipalCoframeCandidate_inv_of_upstream
    {n : WithTop ℕ∞} {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hLSmooth : MatrixFieldContDiffOn n U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice) :
    MatrixFieldContDiffOn n U (fun y =>
      (actualMetricPrincipalCoframeCandidateField4 g choice y)⁻¹) := by
  apply hLSmooth.inv
  intro y hy
  exact actualMetricPrincipalCoframeCandidate_det_ne_zero_of_upstream
    g y choice (hupstream y hy)

/-- The nonsingular inverse is a left inverse of the upstream-selected
actual-metric coframe. -/
theorem actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹ *
        actualMetricPrincipalCoframeCandidateField4 g choice z = 1 := by
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  exact Matrix.nonsing_inv_mul L (isUnit_iff_ne_zero.mpr
    (actualMetricPrincipalCoframeCandidate_det_ne_zero_of_upstream
      g z choice hupstream))

/-- The nonsingular inverse is a right inverse of the upstream-selected
actual-metric coframe. -/
theorem actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    actualMetricPrincipalCoframeCandidateField4 g choice z *
        (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹ = 1 := by
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  exact Matrix.mul_nonsing_inv L (isUnit_iff_ne_zero.mpr
    (actualMetricPrincipalCoframeCandidate_det_ne_zero_of_upstream
      g z choice hupstream))

/-- The upstream-selected coframe carries the inverse coordinate metric to
the canonical contravariant Minkowski metric. -/
theorem actualMetricPrincipalCoframeCandidate_inverseMetric_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    actualMetricPrincipalCoframeCandidateField4 g choice z *
        (coordinateMetricMatrixField4 g z)⁻¹ *
        (actualMetricPrincipalCoframeCandidateField4 g choice z)ᵀ =
      minkowskiMetric := by
  let G := coordinateMetricMatrixField4 g z
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let K := L⁻¹
  have hmetricCov : G = Lᵀ * minkowskiMetric * L := by
    simpa [G, L] using
      (actualMetricPrincipalCoframeCandidate_metric_of_upstream
        g z choice hupstream).symm
  have hKL : K * L = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice hupstream
  have hLK : L * K = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice hupstream
  have hinv := inverse_metric_congruence G L K hmetricCov hKL hLK
  have htrans : Kᵀ * Lᵀ = 1 := by
    rw [← Matrix.transpose_mul, hLK, Matrix.transpose_one]
  rw [show (coordinateMetricMatrixField4 g z)⁻¹ =
      K * minkowskiMetric * Kᵀ by simpa [G] using hinv]
  calc
    L * (K * minkowskiMetric * Kᵀ) * Lᵀ =
        (L * K) * minkowskiMetric * (Kᵀ * Lᵀ) := by
      noncomm_ring
    _ = minkowskiMetric := by rw [hLK, htrans, one_mul, mul_one]

/-- **The exact upstream Hodge gate selects positive orientation.**  The
selected coframe is already nonsingular.  If its determinant were negative,
orientation-reversing Hodge naturality would make the actual Hodge partner
the negative of the transported canonical partner, contradicting the exact
upstream Hodge equality.  Positivity of `q` rules out a zero seed. -/
theorem actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    0 < Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g choice z) := by
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let K := L⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  have hdetNe : Matrix.det L ≠ 0 := by
    simpa [L] using
      actualMetricPrincipalCoframeCandidate_det_ne_zero_of_upstream
        g z choice hupstream
  rcases lt_or_gt_of_ne hdetNe with hneg | hpos
  · exfalso
    have hmetric := actualMetricPrincipalCoframeCandidate_metric_of_upstream
      g z choice hupstream
    have hKL := actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
      g z choice hupstream
    have hLK := actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
      g z choice hupstream
    have hnegative :=
      coordinateMetricHodgeTwoForm4_congruence_of_det_neg
        (coordinateMetricMatrixField4 g z) L K
        (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)
        (by simpa [L] using hmetric.symm)
        (by simpa [L, K] using hKL)
        (by simpa [L, K] using hLK) hneg
    have hhodge : IsActualMetricHodgeCompatibleAt4 g choice z := by
      have hup := hupstream
      unfold IsActualMetricUpstreamEntranceAt4 at hup
      exact hup.2.2.2.2.2.2.2.2.1
    unfold IsActualMetricHodgeCompatibleAt4 at hhodge
    have hnegative' :
        actualMetricHodgeElectricSeedCandidateField4 g choice z =
          -actualMetricTransportedHodgeSeedCandidateField4 g choice z := by
      simpa [L, K, q, actualMetricHodgeElectricSeedCandidateField4,
        actualMetricElectricSeedCandidateField4,
        actualMetricTransportedHodgeSeedCandidateField4,
        transportedPositiveQHodgeSeed,
        coordinateMetricHodgeTwoForm4_minkowski] using hnegative
    have heq : transportedPositiveQHodgeSeed L q =
        -transportedPositiveQHodgeSeed L q := by
      calc
        transportedPositiveQHodgeSeed L q =
            actualMetricHodgeElectricSeedCandidateField4 g choice z := by
              simpa [L, q, actualMetricTransportedHodgeSeedCandidateField4]
                using hhodge.symm
        _ = -actualMetricTransportedHodgeSeedCandidateField4 g choice z :=
          hnegative'
        _ = -transportedPositiveQHodgeSeed L q := by
          simp [L, q, actualMetricTransportedHodgeSeedCandidateField4]
    have hzero : transportedPositiveQHodgeSeed L q = 0 := by
      have hadd : transportedPositiveQHodgeSeed L q +
          transportedPositiveQHodgeSeed L q = 0 :=
        (add_eq_zero_iff_eq_neg).2 heq
      have htwo : (2 : ℝ) • transportedPositiveQHodgeSeed L q = 0 := by
        simpa [two_smul] using hadd
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact (transportedCanonicalHodge_ne_zero L K q
      (by simpa [q] using
        IsActualMetricUpstreamEntranceAt4.qPos g z choice hupstream)
      (by simpa [L, K] using hLK)) hzero
  · simpa [L] using hpos

/-- **The selected actual-metric coframe is Maxwell-adapted.** The upstream
square/projector gates put the first two selected tetrad legs in the negative
principal plane and the last two in the positive principal plane.  Hence the
detector residual is exactly the canonical mixed Maxwell residual in the
selected (possibly orientation-reflected) coframe. -/
theorem actualMetricMaxwellResidual_transport_eq_canonical_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    transportMixed
        (actualMetricPrincipalCoframeCandidateField4 g choice z)
        (actualMetricMaxwellResidualCandidateField4 g choice z)
        (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹ =
      canonicalMaxwellResidual
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z) := by
  let G := coordinateMetricMatrixField4 g z
  let S := actualMetricMaxwellResidualCandidateField4 g choice z
  let qSq := actualRicciReconstructedQSqField4 g z
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  let P := actualMetricMaxwellMinusProjectorCandidateField4 g choice z
  let Q := actualMetricMaxwellPlusProjectorCandidateField4 g choice z
  let Plin := Matrix.toLin' P
  let Qlin := Matrix.toLin' Q
  let T := actualMetricPrincipalTetradCandidateField4 g choice z
  let E := actualMetricPrincipalFrameCandidateField4 g choice z
  have hup := hupstream
  unfold IsActualMetricUpstreamEntranceAt4 at hup
  dsimp only at hup
  rcases hup with
    ⟨halgebraic, _, _, _, _, _, _, hmaxwell, _, hx, hy, hu, hv⟩
  have halg := halgebraic
  unfold IsActualMetricAlgebraicEntranceAt4 at halg
  dsimp only at halg
  have hGsym : Gᵀ = G := by simpa [G] using halg.1
  have hqSqPos : 0 < qSq := by
    simpa [qSq] using halg.2.2.2.2.2.2.1
  have hgsymm : (continuousBilinFormToBilin (g z)).IsSymm := by
    have h : (Matrix.toBilin' G).IsSymm :=
      Matrix.isSymm_toBilin'_iff_isSymm.mpr hGsym
    simpa [G, coordinateMetricMatrixField4_toBilin'] using h
  have hmax := hmaxwell
  unfold IsActualMetricMaxwellEntranceAt4 at hmax
  dsimp only at hmax
  rcases hmax with ⟨hSqRaw, _, hP, hQ, _, _⟩
  have hSq : S * S = q ^ 2 • (1 : Matrix4) := by
    have hqSq : q ^ 2 = qSq := by
      simpa [q, qSq] using positiveMaxwellMagnitudeFromSquare_sq
        (actualRicciReconstructedQSqField4 g) z hqSqPos
    simpa [S, qSq, hqSq] using hSqRaw
  have hPcomp : Plin.comp Plin = Plin := by
    have h' := congrArg Matrix.toLin' hP
    rw [Matrix.toLin'_mul] at h'
    exact h'
  have hQcomp : Qlin.comp Qlin = Qlin := by
    have h' := congrArg Matrix.toLin' hQ
    rw [Matrix.toLin'_mul] at h'
    exact h'
  have hminus0 : Plin
      (actualMetricMaxwellMinusProbe0Field4 g choice z) =
      actualMetricMaxwellMinusProbe0Field4 g choice z := by
    exact projector_apply_fixed Plin hPcomp
      (curvatureCoordinateDirection choice.maxwellMinusProbe0)
  have hminus1 : Plin
      (actualMetricMaxwellMinusProbe1Field4 g choice z) =
      actualMetricMaxwellMinusProbe1Field4 g choice z := by
    exact projector_apply_fixed Plin hPcomp
      (curvatureCoordinateDirection choice.maxwellMinusProbe1)
  have hminus0Matrix : P *ᵥ
      actualMetricMaxwellMinusProbe0Field4 g choice z =
      actualMetricMaxwellMinusProbe0Field4 g choice z := by
    simpa [Plin, Matrix.toLin'_apply] using hminus0
  have hminus1Matrix : P *ᵥ
      actualMetricMaxwellMinusProbe1Field4 g choice z =
      actualMetricMaxwellMinusProbe1Field4 g choice z := by
    simpa [Plin, Matrix.toLin'_apply] using hminus1
  have hpivot : Plin
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice z) =
      actualMetricMaxwellLorentzPivotCandidateField4 g choice z := by
    cases hrecipe : choice.maxwellMinusPivotRecipe <;>
      simp [actualMetricMaxwellLorentzPivotCandidateField4,
        smoothLorentzianPivotCandidate, hrecipe,
        Plin, Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_sub,
        Matrix.mulVec_smul, hminus0Matrix, hminus1Matrix]
  have hcompanion : Plin
      (actualMetricMaxwellLorentzCompanionCandidateField4 g choice z) =
      actualMetricMaxwellLorentzCompanionCandidateField4 g choice z := by
    cases hrecipe : choice.maxwellMinusPivotRecipe <;>
      simp [actualMetricMaxwellLorentzCompanionCandidateField4,
        smoothLorentzianPivotCompanion, hrecipe,
        Plin, Matrix.toLin'_apply, hminus0Matrix, hminus1Matrix]
  have hplus0 : Qlin
      (actualMetricMaxwellPlusProbe0Field4 g choice z) =
      actualMetricMaxwellPlusProbe0Field4 g choice z := by
    exact projector_apply_fixed Qlin hQcomp
      (curvatureCoordinateDirection choice.maxwellPlusProbe0)
  have hplus1 : Qlin
      (actualMetricMaxwellPlusProbe1Field4 g choice z) =
      actualMetricMaxwellPlusProbe1Field4 g choice z := by
    exact projector_apply_fixed Qlin hQcomp
      (curvatureCoordinateDirection choice.maxwellPlusProbe1)
  have hLorFixed :
      Plin T.1.1 = T.1.1 ∧ Plin T.1.2 = T.1.2 := by
    have h := lorentzianPlaneFrame_fixed
      (continuousBilinFormToBilin (g z)) Plin
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice z)
      (actualMetricMaxwellLorentzCompanionCandidateField4 g choice z)
      hpivot hcompanion
    simpa [T, actualMetricPrincipalTetradCandidateField4,
      smoothPrincipalTetradFromFields, smoothLorentzianPlaneFrame,
      smoothNormalizeTimelike, smoothNormalizeSpacelike,
      smoothMetricOrthogonalizeSecond, smoothMetricPairing,
      lorentzianPlaneFrame, normalizeTimelike, normalizeSpacelike,
      metricOrthogonalizeSecond, continuousBilinFormToBilin] using h
  have hSpaceFixed :
      Qlin T.2.1 = T.2.1 ∧ Qlin T.2.2 = T.2.2 := by
    have h := spacelikePlaneFrame_fixed
      (continuousBilinFormToBilin (g z)) Qlin
      (actualMetricMaxwellPlusProbe0Field4 g choice z)
      (actualMetricMaxwellPlusProbe1Field4 g choice z)
      hplus0 hplus1
    simpa [T, actualMetricPrincipalTetradCandidateField4,
      smoothPrincipalTetradFromFields, smoothSpacelikePlaneFrame,
      smoothNormalizeSpacelike, smoothMetricOrthogonalizeSecond,
      smoothMetricPairing, spacelikePlaneFrame, normalizeSpacelike,
      metricOrthogonalizeSecond, continuousBilinFormToBilin] using h
  have hframe : IsPseudoOrthonormalPrincipalTetrad
      (continuousBilinFormToBilin (g z)) T.1 T.2 := by
    simpa [T] using actualMetricPrincipalTetradCandidate_pseudoOrthonormal
      g choice z hgsymm hqSqPos hmaxwell hx hy hu hv
  have hPprojector : Matrix.toLin' P =
      maxwellMinusProjector (Matrix.toLin' S) q := by
    simpa [P, S, q, actualMetricMaxwellMinusProjectorCandidateField4,
      curvatureMaxwellMinusProjectorField,
      matrixMaxwellMinusProjectorField] using
      matrixMaxwellMinusProjector_toLin' S q
  have hQprojector : Matrix.toLin' Q =
      maxwellPlusProjector (Matrix.toLin' S) q := by
    simpa [Q, S, q, actualMetricMaxwellPlusProjectorCandidateField4,
      curvatureMaxwellPlusProjectorField,
      matrixMaxwellPlusProjectorField] using
      matrixMaxwellPlusProjector_toLin' S q
  have hq : 0 < q := by simpa [q] using
    IsActualMetricUpstreamEntranceAt4.qPos g z choice hupstream
  have hSlin : Matrix.toLin' S * Matrix.toLin' S =
      q ^ 2 • (1 : Module.End ℝ (Fin 4 → ℝ)) := by
    have h' := congrArg Matrix.toLin' hSq
    rw [Matrix.toLin'_mul] at h'
    simpa [map_smul, Matrix.toLin'_one, Module.End.one_eq_id,
      Module.End.mul_eq_comp] using h'
  have hs0 : Matrix.toLin' S T.1.1 = (-q) • T.1.1 := by
    apply maxwellResidual_apply_eq_neg_smul_of_minus_fixed
      (Matrix.toLin' S) q (ne_of_gt hq) hSlin
    rw [← hPprojector]
    simpa [Plin] using hLorFixed.1
  have hs1 : Matrix.toLin' S T.1.2 = (-q) • T.1.2 := by
    apply maxwellResidual_apply_eq_neg_smul_of_minus_fixed
      (Matrix.toLin' S) q (ne_of_gt hq) hSlin
    rw [← hPprojector]
    simpa [Plin] using hLorFixed.2
  have hs2 : Matrix.toLin' S T.2.1 = q • T.2.1 := by
    apply maxwellResidual_apply_eq_smul_of_plus_fixed
      (Matrix.toLin' S) q (ne_of_gt hq) hSlin
    rw [← hQprojector]
    simpa [Qlin] using hSpaceFixed.1
  have hs3 : Matrix.toLin' S T.2.2 = q • T.2.2 := by
    apply maxwellResidual_apply_eq_smul_of_plus_fixed
      (Matrix.toLin' S) q (ne_of_gt hq) hSlin
    rw [← hQprojector]
    simpa [Qlin] using hSpaceFixed.2
  have hSE : S * E = E * canonicalMaxwellResidual q := by
    ext i j
    fin_cases j
    · have h := congrFun hs0 i
      simpa [Matrix.toLin'_apply, E,
        actualMetricPrincipalFrameCandidateField4,
        smoothPrincipalFrameMatrix, smoothPrincipalTetradVector,
        principalTetradVectors, canonicalMaxwellResidual,
        Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, mul_comm] using h
    · have h := congrFun hs1 i
      simpa [Matrix.toLin'_apply, E,
        actualMetricPrincipalFrameCandidateField4,
        smoothPrincipalFrameMatrix, smoothPrincipalTetradVector,
        principalTetradVectors, canonicalMaxwellResidual,
        Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, mul_comm] using h
    · have h := congrFun hs2 i
      simpa [Matrix.toLin'_apply, E,
        actualMetricPrincipalFrameCandidateField4,
        smoothPrincipalFrameMatrix, smoothPrincipalTetradVector,
        principalTetradVectors, canonicalMaxwellResidual,
        Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, mul_comm] using h
    · have h := congrFun hs3 i
      simpa [Matrix.toLin'_apply, E,
        actualMetricPrincipalFrameCandidateField4,
        smoothPrincipalFrameMatrix, smoothPrincipalTetradVector,
        principalTetradVectors, canonicalMaxwellResidual,
        Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, mul_comm] using h
  have hframeMetric : Eᵀ * G * E = minkowskiMetric := by
    simpa [E, G, T, actualMetricPrincipalFrameCandidateField4] using
      smoothPrincipalFrameMatrix_metric
        (actualMetricPrincipalTetradCandidateField4 g choice) z
        (continuousBilinFormToBilin (g z))
        (coordinateMetricMatrixField4 g z)
        (coordinateMetricMatrixField4_toBilin' g z) hgsymm hframe
  have hdetE : Matrix.det E ≠ 0 := by
    intro hzero
    have hd := congrArg Matrix.det hframeMetric
    simp [Matrix.det_mul, hzero, minkowskiMetric_det] at hd
  have hunitE : IsUnit (Matrix.det E) := isUnit_iff_ne_zero.mpr hdetE
  have hEinvE : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hunitE
  have hbase : E⁻¹ * S * E = canonicalMaxwellResidual q := by
    calc
      E⁻¹ * S * E = E⁻¹ * (S * E) := by noncomm_ring
      _ = E⁻¹ * (E * canonicalMaxwellResidual q) := by rw [hSE]
      _ = (E⁻¹ * E) * canonicalMaxwellResidual q := by noncomm_ring
      _ = canonicalMaxwellResidual q := by rw [hEinvE, one_mul]
  have hRR : principalOrientationReflection4 *
      principalOrientationReflection4 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [principalOrientationReflection4, Matrix.mul_apply,
        Fin.sum_univ_succ]
  have hRcanonical : principalOrientationReflection4 *
      canonicalMaxwellResidual q * principalOrientationReflection4 =
        canonicalMaxwellResidual q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [principalOrientationReflection4, canonicalMaxwellResidual,
        Matrix.mul_apply, Fin.sum_univ_succ]
  cases horient : choice.orientationReverse
  · have hK : E⁻¹⁻¹ = E := Matrix.inv_eq_right_inv hEinvE
    simpa [transportMixed, actualMetricPrincipalCoframeCandidateField4,
      orientPrincipalCoframe4, horient, E, S, q, hK] using hbase
  · have hK : (principalOrientationReflection4 * E⁻¹)⁻¹ =
        E * principalOrientationReflection4 := by
      apply Matrix.inv_eq_right_inv
      calc
        (principalOrientationReflection4 * E⁻¹) *
            (E * principalOrientationReflection4) =
          principalOrientationReflection4 * (E⁻¹ * E) *
            principalOrientationReflection4 := by noncomm_ring
        _ = 1 := by rw [hEinvE, mul_one, hRR]
    simp only [transportMixed, actualMetricPrincipalCoframeCandidateField4,
      orientPrincipalCoframe4, horient, ↓reduceIte]
    rw [hK]
    calc
      (principalOrientationReflection4 * E⁻¹) * S *
          (E * principalOrientationReflection4) =
        principalOrientationReflection4 * (E⁻¹ * S * E) *
          principalOrientationReflection4 := by noncomm_ring
      _ = canonicalMaxwellResidual q := by rw [hbase, hRcanonical]

/-- **Pointwise physical Maxwell orbit for an upstream actual-metric
branch.** If a skew physical two-form has Maxwell stress equal to the
metric-reconstructed Ricci residual, the upstream-selected coframe pulls it
back to exactly one unit-circle duality orbit of the positive canonical seed.
The physical form is an explicit correctness witness here; it is not an input
to the metric-only detector. -/
theorem exists_actualMetricDualityParameter_of_upstream_physicalStress
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (F : Matrix4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hF : Fᵀ = -F)
    (hstress : matrixMaxwellStress
        (coordinateMetricMatrixField4 g z)⁻¹ F =
      actualMetricMaxwellResidualCandidateField4 g choice z) :
    ∃ p : DualityParameter,
      transportTwoForm
          (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹ F =
        p.c • canonicalMaxwellTwoForm
            (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
              (actualRicciReconstructedQSqField4 g) z)) 0 +
          p.s • canonicalHodgeStar
            (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
              (actualRicciReconstructedQSqField4 g) z)) 0 := by
  let G := coordinateMetricMatrixField4 g z
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let K := L⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  have hKL : K * L = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice hupstream
  have hLK : L * K = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice hupstream
  have hmetricInv : L * G⁻¹ * Lᵀ = minkowskiMetric := by
    simpa [G, L] using
      actualMetricPrincipalCoframeCandidate_inverseMetric_of_upstream
        g z choice hupstream
  have hcanonical :
      transportMixed L (matrixMaxwellStress G⁻¹ F) K =
        canonicalMaxwellResidual q := by
    rw [show matrixMaxwellStress G⁻¹ F =
        actualMetricMaxwellResidualCandidateField4 g choice z by
      simpa [G] using hstress]
    simpa [L, K, q] using
      actualMetricMaxwellResidual_transport_eq_canonical_of_upstream
        g z choice hupstream
  simpa [G, L, K, q] using
    exists_dualityParameter_of_adaptedMaxwellStress
      G⁻¹ L K F q
      (by simpa [q] using
        IsActualMetricUpstreamEntranceAt4.qPos g z choice hupstream)
      hKL hLK hmetricInv hF hcanonical

/-- **Patchwise physical Maxwell orbit for one fixed actual-metric branch.**
On a patch where the same finite detector choice passes the upstream gates, a
smooth physical skew two-form whose Maxwell stress is the reconstructed
residual has explicit smooth unit-circle complexion coordinates in the
selected principal frame.  Smoothness of the positive magnitude and inverse
coframe is stated explicitly: pointwise upstream algebra alone does not imply
these analytic hypotheses. -/
theorem smoothActualMetricAdaptedMaxwellStressFiber_coordinates_of_upstream
    {n : WithTop ℕ∞} {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (F : CurvatureCoordinateSpace4 → Matrix4)
    (hqSmooth : ContDiffOn ℝ n
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hKSmooth : MatrixFieldContDiffOn n U (fun y =>
      (actualMetricPrincipalCoframeCandidateField4 g choice y)⁻¹))
    (hFSmooth : MatrixFieldContDiffOn n U F)
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hskew : ∀ y ∈ U, (F y)ᵀ = -F y)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹ (F y) =
        actualMetricMaxwellResidualCandidateField4 g choice y) :
    let L := actualMetricPrincipalCoframeCandidateField4 g choice
    let K := fun y => (L y)⁻¹
    let q := positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g)
    let pulledF := fun y => transportTwoForm (K y) (F y)
    ContDiffOn ℝ n (smoothCanonicalStressFiberCosine q pulledF) U ∧
      ContDiffOn ℝ n (smoothCanonicalStressFiberSine q pulledF) U ∧
      (∀ y ∈ U,
        smoothCanonicalStressFiberCosine q pulledF y ^ 2 +
          smoothCanonicalStressFiberSine q pulledF y ^ 2 = 1) ∧
      ∀ y ∈ U,
        pulledF y = smoothCanonicalStressFiberCosine q pulledF y •
              canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
            smoothCanonicalStressFiberSine q pulledF y •
              canonicalHodgeStar (Real.sqrt (2 * q y)) 0 := by
  dsimp only
  let GInv := fun y => (coordinateMetricMatrixField4 g y)⁻¹
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let K := fun y => (L y)⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g)
  have hq : ∀ y ∈ U, 0 < q y := by
    intro y hy
    simpa [q] using
      IsActualMetricUpstreamEntranceAt4.qPos g y choice
        (hupstream y hy)
  have hKL : ∀ y ∈ U, K y * L y = 1 := by
    intro y hy
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g y choice (hupstream y hy)
  have hLK : ∀ y ∈ U, L y * K y = 1 := by
    intro y hy
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g y choice (hupstream y hy)
  have hmetric : ∀ y ∈ U,
      L y * GInv y * (L y)ᵀ = minkowskiMetric := by
    intro y hy
    simpa [GInv, L] using
      actualMetricPrincipalCoframeCandidate_inverseMetric_of_upstream
        g y choice (hupstream y hy)
  have hcanonical : ∀ y ∈ U,
      transportMixed (L y)
          (matrixMaxwellStress (GInv y) (F y)) (K y) =
        canonicalMaxwellResidual (q y) := by
    intro y hy
    rw [show matrixMaxwellStress (GInv y) (F y) =
        actualMetricMaxwellResidualCandidateField4 g choice y by
      simpa [GInv] using hstress y hy]
    simpa [L, K, q] using
      actualMetricMaxwellResidual_transport_eq_canonical_of_upstream
        g y choice (hupstream y hy)
  simpa [GInv, L, K, q] using
    smoothAdaptedMaxwellStressFiber_coordinates
      GInv L K F q hqSmooth hKSmooth hFSmooth hq
        hKL hLK hmetric hskew hcanonical

/-- A genuine physical matrix `C¹` realization supplies the smoothness and
skewness hypotheses of the actual-metric stress-fibre theorem automatically.
This is the field-level form used by the EMD germ splice. -/
theorem smoothActualMetricAdaptedMaxwellStressFiber_coordinates_of_c1
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (physicalF : RescaledMaxwellMatrixC1On U)
    (hopen : IsOpen U)
    (hqSmooth : ContDiffOn ℝ 1
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hKSmooth : MatrixFieldContDiffOn 1 U (fun y ↦
      (actualMetricPrincipalCoframeCandidateField4 g choice y)⁻¹))
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y) :
    let L := actualMetricPrincipalCoframeCandidateField4 g choice
    let K := fun y ↦ (L y)⁻¹
    let q := positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g)
    let pulledF := fun y ↦ transportTwoForm (K y) (physicalF.field y)
    ContDiffOn ℝ 1 (smoothCanonicalStressFiberCosine q pulledF) U ∧
      ContDiffOn ℝ 1 (smoothCanonicalStressFiberSine q pulledF) U ∧
      (∀ y ∈ U,
        smoothCanonicalStressFiberCosine q pulledF y ^ 2 +
          smoothCanonicalStressFiberSine q pulledF y ^ 2 = 1) ∧
      ∀ y ∈ U,
        pulledF y = smoothCanonicalStressFiberCosine q pulledF y •
              canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
            smoothCanonicalStressFiberSine q pulledF y •
              canonicalHodgeStar (Real.sqrt (2 * q y)) 0 := by
  exact smoothActualMetricAdaptedMaxwellStressFiber_coordinates_of_upstream
    g choice physicalF.field hqSmooth hKSmooth
      (physicalF.contDiffOn_field hopen) hupstream physicalF.alternating
        hstress

/-- **Patchwise C1 physical-germ splice.**  Genuine rescaled Maxwell and
Hodge fields satisfying the exterior EMD equations transfer those equations
to the actual transported positive-`q` seed whenever their germs agree with
the displayed rotated seed fields.  The resulting neighborhood channel
identity feeds the literal quotient derivative, so the complete physical
constant-coupling predicate follows without an acceptance hypothesis.

The source component enters only through its nonvanishing germ.  In
particular, the wedge-component indices used later by the genericity test do
not occur in this theorem. -/
theorem isPhysicalConstantCouplingChannel_of_patch_physicalSeedGerms
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (a : ℝ) (source : Fin 4) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hLSmooth : MatrixFieldContDiffOn 2 U L)
    (hqSmooth : ContDiffOn ℝ 2 q U)
    (hqPos : ∀ y ∈ U, 0 < q y)
    (hcSmooth : ContDiffOn ℝ 1 c U)
    (hsSmooth : ContDiffOn ℝ 1 s U)
    (hunit : ∀ y ∈ U, c y ^ 2 + s y ^ 2 = 1)
    (hdc : ∀ y ∈ U,
      scalarFieldCoordinateFDeriv c y = (-s y) • omega y)
    (hds : ∀ y ∈ U,
      scalarFieldCoordinateFDeriv s y = c y • omega y)
    (hLK : ∀ y ∈ U, L y * (L y)⁻¹ = 1)
    (hsource : ∀ᶠ y in nhds z,
      pullCovectorToPrincipalFrame (L y)⁻¹ (v y) source ≠ 0)
    (hgerms :
      let M := PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s a hdc hds
      ∀ y ∈ U,
        physicalF.field =ᶠ[nhds y]
            (fun x ↦ (M.exteriorJet x).rotatedF) ∧
          physicalG.field =ᶠ[nhds y]
            (fun x ↦ (M.exteriorJet x).rotatedG))
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo (v y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y))) :
    IsPhysicalConstantCouplingChannel (Real.sqrt (2 * q z))
      (pullCovectorToPrincipalFrame (L z)⁻¹ (v z))
      (pullCovectorToPrincipalFrame (L z)⁻¹
        (curvatureSeedCosineCoordinateDerivative L q v source z))
      (curvatureSeedCanonicalChannelField L q z) a := by
  let M := PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
    L q omega c s a hdc hds
  let S : PositiveQPhaseIIISeedPairC1Realization M :=
    PositiveQPhaseIIISeedPairC1Realization.ofActualSmoothFields
      L q omega c s a hdc hds hopen hLSmooth hqSmooth hqPos
        hcSmooth hsSmooth
  have hchannels : ∀ᶠ y in nhds z,
      curvatureSeedCanonicalChannelField L q y =
        canonicalPhysicalSeedChannels (Real.sqrt (2 * q y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (v y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (omega y))
          (a * (c y ^ 2 - s y ^ 2)) (a * (2 * c y * s y)) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    have hyGerms := hgerms y hy
    have hFrealized : physicalF.field =ᶠ[nhds y] S.rotatedC1.field := by
      filter_upwards [hyGerms.1, hopen.mem_nhds hy] with x hx hxU
      calc
        physicalF.field x = (M.exteriorJet x).rotatedF := hx
        _ = S.rotatedC1.field x :=
          (S.toRescaledMaxwellC1Realization.field_eq x hxU).symm
    have hGrealized :
        physicalG.field =ᶠ[nhds y] S.rotatedHodgeC1.field := by
      filter_upwards [hyGerms.2, hopen.mem_nhds hy] with x hx hxU
      calc
        physicalG.field x = (M.exteriorJet x).rotatedG := hx
        _ = S.rotatedHodgeC1.field x :=
          (S.toRescaledMaxwellC1PairRealization.hodge_field_eq x hxU).symm
    have hseedClosure : EMDExteriorClosure matrixOneWedgeTwo (v y) a
        (M.exteriorJet y).rotatedF (M.exteriorJet y).rotatedG
        ((M.exteriorJet y).rotatedDF matrixOneWedgeTwo)
        ((M.exteriorJet y).rotatedDG matrixOneWedgeTwo) :=
      S.exteriorJet_emdExteriorClosure_of_physicalFields_eventuallyEq
        physicalF physicalG y hy (v y) a hFrealized hGrealized
          (hclosure y hy)
    unfold curvatureSeedCanonicalChannelField
    simpa [M, PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
      matrixFieldCoordinateFDeriv4] using
      transportedPositiveQCanonicalSeedChannels_eq_physical_of_emdClosure
        (L y) (L y)⁻¹ (matrixFieldCoordinateFDeriv4 L y)
        (q y) (scalarFieldCoordinateFDeriv q y) (v y) (omega y) a
        (c y) (s y) (scalarFieldCoordinateFDeriv c y)
        (scalarFieldCoordinateFDeriv s y) (hLK y hy) (hunit y hy)
        (hdc y hy) (hds y hy) hseedClosure
  apply isPhysicalConstantCouplingChannel_of_physicalSeedChannelGerm
    L q v omega a c s source z
  · filter_upwards [hopen.mem_nhds hz] with y hy
    exact hqPos y hy
  · exact hsource
  · exact hchannels
  · exact ((hcSmooth.differentiableOn_one z hz).differentiableAt
      (hopen.mem_nhds hz))
  · exact ((hsSmooth.differentiableOn_one z hz).differentiableAt
      (hopen.mem_nhds hz))
  · exact hunit z hz
  · exact hdc z hz
  · exact hds z hz

/-- Componentwise continuity of a frame field and covector field is
preserved by principal-frame pullback. -/
theorem continuousOn_pullCovectorToPrincipalFrame_component
    {U : Set CurvatureCoordinateSpace4}
    (K : CurvatureCoordinateSpace4 → Matrix4)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (source : Fin 4)
    (hK : ∀ i, ContinuousOn (fun y ↦ K y i source) U)
    (hv : ∀ i, ContinuousOn (fun y ↦ v y i) U) :
    ContinuousOn
      (fun y ↦ pullCovectorToPrincipalFrame (K y) (v y) source) U := by
  unfold pullCovectorToPrincipalFrame
  apply continuousOn_finsetSum Finset.univ
  intro i _
  exact (hK i).mul (hv i)

/-- **Actual-metric patchwise physical-channel theorem.**  On one fixed
upstream branch, a smooth physical Maxwell field with the reconstructed
stress determines explicit smooth stress-fibre coordinates.  The adapted
stress-fibre complexion theorem then supplies a single complexion one-form
field on the patch.  If genuine `C¹` physical Maxwell/Hodge fields have the
displayed rotated actual-seed germs and satisfy exterior EMD closure, the
selected source obeys the full actual-metric physical-channel predicate.

The germ hypotheses are the remaining geometric splice.  They concern
actual fields and actual transported seeds, not detector acceptance or a
prepackaged channel identity. -/
theorem isActualMetricPhysicalConstantCouplingChannelAt_of_patch_physicalFields
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (a : ℝ) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hLSmooth : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hqSmooth : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hKSmooth : MatrixFieldContDiffOn 1 U (fun y ↦
      (actualMetricPrincipalCoframeCandidateField4 g choice y)⁻¹))
    (hFSmooth : MatrixFieldContDiffOn 1 U physicalF.field)
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y)
    (hvContinuous : ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y i) U)
    (hsource :
      pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) choice.channel.1 ≠ 0)
    (hgerms :
      let L := actualMetricPrincipalCoframeCandidateField4 g choice
      let q := positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)
      let K := fun y ↦ (L y)⁻¹
      let pulledF := fun y ↦ transportTwoForm (K y) (physicalF.field y)
      let c := smoothCanonicalStressFiberCosine q pulledF
      let s := smoothCanonicalStressFiberSine q pulledF
      ∀ y ∈ U,
        physicalF.field =ᶠ[nhds y] (fun x ↦
            (localPositiveQExteriorDualityJet
              (L x) (fun k i j ↦
                scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
              (q x) (scalarFieldCoordinateFDeriv q x)
              (c x) (s x) (scalarFieldCoordinateFDeriv c x)
              (scalarFieldCoordinateFDeriv s x)).rotatedF) ∧
          physicalG.field =ᶠ[nhds y] (fun x ↦
            (localPositiveQExteriorDualityJet
              (L x) (fun k i j ↦
                scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
              (q x) (scalarFieldCoordinateFDeriv q x)
              (c x) (s x) (scalarFieldCoordinateFDeriv c x)
              (scalarFieldCoordinateFDeriv s x)).rotatedG))
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y))) :
    IsPhysicalConstantCouplingChannel
      (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z))
      (pullCovectorToPrincipalFrame
        (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z))
      (pullCovectorToPrincipalFrame
        (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
        (curvatureSeedCosineCoordinateDerivative
          (actualMetricPrincipalCoframeCandidateField4 g choice)
          (positiveMaxwellMagnitudeFromSquare
            (actualRicciReconstructedQSqField4 g))
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus) choice.channel.1 z))
      (curvatureSeedCanonicalChannelField
        (actualMetricPrincipalCoframeCandidateField4 g choice)
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z) a := by
  classical
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g)
  let K := fun y ↦ (L y)⁻¹
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus
  let pulledF := fun y ↦ transportTwoForm (K y) (physicalF.field y)
  let c := smoothCanonicalStressFiberCosine q pulledF
  let s := smoothCanonicalStressFiberSine q pulledF
  have hqPos : ∀ y ∈ U, 0 < q y := by
    intro y hy
    simpa [q] using
      IsActualMetricUpstreamEntranceAt4.qPos g y choice
        (hupstream y hy)
  have hKL : ∀ y ∈ U, K y * L y = 1 := by
    intro y hy
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g y choice (hupstream y hy)
  have hLK : ∀ y ∈ U, L y * K y = 1 := by
    intro y hy
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g y choice (hupstream y hy)
  let GInv := fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹
  have hmetric : ∀ y ∈ U,
      L y * GInv y * (L y)ᵀ = minkowskiMetric := by
    intro y hy
    simpa [GInv, L] using
      actualMetricPrincipalCoframeCandidate_inverseMetric_of_upstream
        g y choice (hupstream y hy)
  have hcanonical : ∀ y ∈ U,
      transportMixed (L y)
          (matrixMaxwellStress (GInv y) (physicalF.field y)) (K y) =
        canonicalMaxwellResidual (q y) := by
    intro y hy
    rw [show matrixMaxwellStress (GInv y) (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y by
      simpa [GInv] using hstress y hy]
    simpa [L, K, q] using
      actualMetricMaxwellResidual_transport_eq_canonical_of_upstream
        g y choice (hupstream y hy)
  have hstressFiber :
      ContDiffOn ℝ 1 c U ∧ ContDiffOn ℝ 1 s U ∧
        (∀ y ∈ U, c y ^ 2 + s y ^ 2 = 1) ∧
        ∀ y ∈ U,
          pulledF y = c y •
                canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
              s y • canonicalHodgeStar (Real.sqrt (2 * q y)) 0 := by
    simpa [L, K, q, pulledF, c, s] using
      smoothActualMetricAdaptedMaxwellStressFiber_coordinates_of_upstream
        (n := (1 : WithTop ℕ∞)) g choice physicalF.field
        (hqSmooth.of_le (by norm_num)) hKSmooth hFSmooth hupstream
        physicalF.alternating hstress
  have homegaAt : ∀ y ∈ U, ∃ w : OneForm4,
      scalarFieldCoordinateFDeriv c y = (-s y) • w ∧
        scalarFieldCoordinateFDeriv s y = c y • w := by
    intro y hy
    have H := exists_complexionOneForm_of_smoothAdaptedMaxwellStressFiber
      GInv L K physicalF.field q y hopen hy
      (hqSmooth.of_le (by norm_num)) hKSmooth hFSmooth hqPos
      hKL hLK hmetric physicalF.alternating hcanonical
    simpa [pulledF, c, s] using H.2.2.2.2
  let omega : CurvatureCoordinateSpace4 → OneForm4 := fun y ↦
    if hy : y ∈ U then Classical.choose (homegaAt y hy) else 0
  have hdc : ∀ y ∈ U,
      scalarFieldCoordinateFDeriv c y = (-s y) • omega y := by
    intro y hy
    simpa [omega, hy] using (Classical.choose_spec (homegaAt y hy)).1
  have hds : ∀ y ∈ U,
      scalarFieldCoordinateFDeriv s y = c y • omega y := by
    intro y hy
    simpa [omega, hy] using (Classical.choose_spec (homegaAt y hy)).2
  let M := PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
    L q omega c s a hdc hds
  have hgermsM : ∀ y ∈ U,
      physicalF.field =ᶠ[nhds y]
          (fun x ↦ (M.exteriorJet x).rotatedF) ∧
        physicalG.field =ᶠ[nhds y]
          (fun x ↦ (M.exteriorJet x).rotatedG) := by
    intro y hy
    simpa [M, L, q, K, pulledF, c, s,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
      PositiveQPhaseIIIPatch4.exteriorJet,
      matrixFieldCoordinateFDeriv4] using hgerms y hy
  have hsourceGerm : ∀ᶠ y in nhds z,
      pullCovectorToPrincipalFrame (L y)⁻¹ (v y)
        choice.channel.1 ≠ 0 := by
    have hcontinuous : ContinuousOn
        (fun y ↦ pullCovectorToPrincipalFrame (K y) (v y)
          choice.channel.1) U :=
      continuousOn_pullCovectorToPrincipalFrame_component K v
        choice.channel.1
        (fun i ↦ (hKSmooth i choice.channel.1).continuousOn)
        (by simpa [v] using hvContinuous)
    exact ((hcontinuous z hz).continuousAt (hopen.mem_nhds hz)).eventually_ne
      (by simpa [L, K, v] using hsource)
  exact isPhysicalConstantCouplingChannel_of_patch_physicalSeedGerms
    L q v omega c s physicalF physicalG a choice.channel.1 z
    hopen hz hLSmooth hqSmooth hqPos hstressFiber.1 hstressFiber.2.1
    hstressFiber.2.2.1 hdc hds hLK hsourceGerm
    hgermsM (by simpa [v] using hclosure)

/-- The complete metric-only predicate exposes, in particular, the accepted
curvature-seed branch consumed by the fourth-order confluence theorem. -/
theorem IsActualMetricFourthOrderDetectorCandidateAt.toCurvatureSeed
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (h : IsActualMetricFourthOrderDetectorCandidateAt g z choice) :
    IsCurvatureSeedFourthOrderCandidateAt
      (actualMetricPrincipalCoframeCandidateField4 g choice)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus)
      z choice.channel := by
  exact h.2

/-- The complete metric-only predicate also exposes its actual metric-Hodge
compatibility test. -/
theorem IsActualMetricFourthOrderDetectorCandidateAt.toHodgeCompatible
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (h : IsActualMetricFourthOrderDetectorCandidateAt g z choice) :
    IsActualMetricHodgeCompatibleAt4 g choice z := by
  have hupstream := h.1
  unfold IsActualMetricUpstreamEntranceAt4 at hupstream
  rcases hupstream with
    ⟨_, _, _, _, _, _, _, _, hhodge, _⟩
  exact hhodge

/-- The promised finite actual-metric detector output: filter the finite raw
choice space by the complete obstruction predicate. -/
noncomputable def acceptedActualMetricFourthOrderDetectorChoicesAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    Finset ActualMetricDetectorChoice4 := by
  classical
  exact allActualMetricDetectorChoices4.filter
    (IsActualMetricFourthOrderDetectorCandidateAt g z)

/-- Squared coupling carried by one completely metric-constructed detector
choice. -/
noncomputable def actualMetricFourthOrderCouplingSqCandidateAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) : ℝ :=
  curvatureSeedFourthOrderCouplingSqCandidateAt
    (actualMetricPrincipalCoframeCandidateField4 g choice)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g))
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus)
    z choice.channel

/-- Exact membership statement for the finite metric-only detector. -/
theorem mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ↔
      IsActualMetricFourthOrderDetectorCandidateAt g z choice := by
  classical
  simp [acceptedActualMetricFourthOrderDetectorChoicesAt,
    mem_allActualMetricDetectorChoices4]

/-- Patchwise metric-only acceptance makes the actual metric Hodge field and
the transported canonical Hodge partner equal near every patch point. -/
theorem actualMetricHodgeSeedFields_eventuallyEq_of_patchAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hchoice : ∀ y ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g y choice) :
    actualMetricHodgeElectricSeedCandidateField4 g choice =ᶠ[nhds z]
      actualMetricTransportedHodgeSeedCandidateField4 g choice := by
  filter_upwards [hopen.mem_nhds hz] with y hy
  exact (hchoice y hy).toHodgeCompatible

/-- **Actual Hodge derivative splice.** Acceptance throughout an open patch
identifies not only the two Hodge representatives but their genuine
coordinate Frechet derivatives at every patch point.  Thus the Hodge
exterior channel is metric-derived at the differential order consumed by the
detector. -/
theorem actualMetricHodgeSeedCoordinateFDerivs_eq_of_patchAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hchoice : ∀ y ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g y choice) :
    matrixFieldCoordinateFDeriv4
        (actualMetricHodgeElectricSeedCandidateField4 g choice) z =
      matrixFieldCoordinateFDeriv4
        (actualMetricTransportedHodgeSeedCandidateField4 g choice) z := by
  have hfield :=
    actualMetricHodgeSeedFields_eventuallyEq_of_patchAcceptance
      g choice z hopen hz hchoice
  funext k i j
  have hcomponent :
      (fun y => actualMetricHodgeElectricSeedCandidateField4
        g choice y i j) =ᶠ[nhds z]
      (fun y => actualMetricTransportedHodgeSeedCandidateField4
        g choice y i j) := by
    filter_upwards [hfield] with y hy
    rw [hy]
  unfold matrixFieldCoordinateFDeriv4 scalarFieldCoordinateFDeriv
  rw [Filter.EventuallyEq.fderiv_eq hcomponent]

/-- Physical constant-coupling compatibility specialized to the fields that
the metric-only detector actually constructs.  This is a correctness
predicate, not detector input: `L`, `q`, `v`, both exterior channels, and the
actual `dA` are all fixed formulas in the metric and the finite raw choice. -/
def IsActualMetricPhysicalConstantCouplingChannelAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ) : Prop :=
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g)
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus
  IsPhysicalConstantCouplingChannel
    (Real.sqrt (2 * q z))
    (pullCovectorToPrincipalFrame (L z)⁻¹ (v z))
    (pullCovectorToPrincipalFrame (L z)⁻¹
      (curvatureSeedCosineCoordinateDerivative L q v
        choice.channel.1 z))
    (curvatureSeedCanonicalChannelField L q z) a

/-- The actual-metric physical-channel predicate depends on a finite channel
choice only through its source component.  The two wedge indices belong to
the later genericity gate and can be changed freely here. -/
theorem isActualMetricPhysicalConstantCouplingChannelAt_withChannel_iff_of_source_eq
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (channel channel' : FourthOrderComponentChoice)
    (a : ℝ) (hsource : channel.1 = channel'.1) :
    IsActualMetricPhysicalConstantCouplingChannelAt
        g z (base.withChannel channel) a ↔
      IsActualMetricPhysicalConstantCouplingChannelAt
        g z (base.withChannel channel') a := by
  rcases channel with ⟨source, left, right⟩
  rcases channel' with ⟨source', left', right'⟩
  dsimp only at hsource
  subst source'
  unfold IsActualMetricPhysicalConstantCouplingChannelAt
  rw [actualMetricPrincipalCoframeCandidateField4_withChannel,
    actualMetricPrincipalCoframeCandidateField4_withChannel]
  rfl

/-- A genuine constant-coupling EMD realization of the fields constructed by
one raw metric choice.  This is used only for the necessity/correctness
direction.  In particular, none of `a,c,s,omega,dc,ds` is detector input:
the coframe, positive seed magnitude, scalar covector, both seed derivatives,
and `dA` in the equations below are the fixed metric formulas above. -/
def IsActualMetricConstantCouplingEMDRealizationAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ) : Prop :=
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g)
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus
  let dA := curvatureSeedCosineCoordinateDerivative L q v
    choice.channel.1 z
  ∃ c s : ℝ, ∃ omega dc ds : OneForm4,
    L z * (L z)⁻¹ = 1 ∧
    c ^ 2 + s ^ 2 = 1 ∧
    dc = (-s) • omega ∧
    ds = c • omega ∧
    dA = doubleAngleCosineFirstDerivative a c s dc ds ∧
    let J := localPositiveQExteriorDualityJet (L z)
      (matrixFieldCoordinateFDeriv4 L z) (q z)
      (scalarFieldCoordinateFDeriv q z) c s dc ds
    EMDExteriorClosure matrixOneWedgeTwo (v z) a J.rotatedF J.rotatedG
      (J.rotatedDF matrixOneWedgeTwo)
      (J.rotatedDG matrixOneWedgeTwo)

/-- **The remaining physical predicate is a theorem, not an assumption.**
A genuine EMD realization of the actual metric-constructed seed implies the
physical-channel compatibility consumed by accepted-branch correctness. -/
theorem isActualMetricPhysicalConstantCouplingChannelAt_of_emdRealization
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hEMD : IsActualMetricConstantCouplingEMDRealizationAt
      g z choice a) :
    IsActualMetricPhysicalConstantCouplingChannelAt g z choice a := by
  unfold IsActualMetricConstantCouplingEMDRealizationAt at hEMD
  dsimp only at hEMD
  rcases hEMD with
    ⟨c, s, omega, dc, ds, hLK, hunit, hdc, hds, hdA, hclosure⟩
  unfold IsActualMetricPhysicalConstantCouplingChannelAt
  dsimp only
  unfold curvatureSeedCanonicalChannelField
  exact isPhysicalConstantCouplingChannel_transported_of_emdClosure
    (actualMetricPrincipalCoframeCandidateField4 g choice z)
    (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
    (matrixFieldCoordinateFDeriv4
      (actualMetricPrincipalCoframeCandidateField4 g choice) z)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) z)
    (scalarFieldCoordinateFDeriv
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) z)
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z)
    omega
    (curvatureSeedCosineCoordinateDerivative
      (actualMetricPrincipalCoframeCandidateField4 g choice)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus) choice.channel.1 z)
    a c s dc ds hLK hunit hdc hds hdA hclosure

/-- The two finite component conditions defining the generic fourth-order
branch for one actual-metric raw choice. -/
def IsActualMetricGenericFourthOrderComponentAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) : Prop :=
  pullCovectorToPrincipalFrame
      (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus z) choice.channel.1 ≠ 0 ∧
  oneFormWedgeOneComponent
      (canonicalEffectiveOneFormFromChannels
        (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z))
        (curvatureSeedCanonicalChannelField
          (actualMetricPrincipalCoframeCandidateField4 g choice)
          (positiveMaxwellMagnitudeFromSquare
            (actualRicciReconstructedQSqField4 g)) z))
      (canonicalPrincipalReflectionCovector
        (pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z)))
      choice.channel.2.1 choice.channel.2.2 ≠ 0

/-- Channel-independent form of the genuine fourth-order genericity gate.
It says that the effective curvature channel is not parallel to the
principal reflection of the reconstructed scalar covector. -/
def IsActualMetricActiveFourthOrderWedgeAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) : Prop :=
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let v := pullCovectorToPrincipalFrame (L z)⁻¹
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z)
  let eta := canonicalEffectiveOneFormFromChannels
    (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) z))
    (curvatureSeedCanonicalChannelField L
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) z)
  ∃ left right : Fin 4,
    oneFormWedgeOneComponent eta
      (canonicalPrincipalReflectionCovector v) left right ≠ 0

/-- On the intrinsic active-wedge locus, the finite channel enumeration
contains a source and wedge component satisfying the displayed generic gate.
This is existential: demanding genericity for every enumerated channel would
be impossible because diagonal wedge choices are deliberately enumerated and
rejected. -/
theorem exists_actualMetricGenericFourthOrderComponentAt_withChannel
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z base) :
    ∃ channel : FourthOrderComponentChoice,
      IsActualMetricGenericFourthOrderComponentAt
        g z (base.withChannel channel) := by
  unfold IsActualMetricActiveFourthOrderWedgeAt at hactive
  dsimp only at hactive
  obtain ⟨channel, hsource, hwedge⟩ :=
    exists_fourthOrderComponentChoice_of_activeWedge
      (canonicalEffectiveOneFormFromChannels
        (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z))
        (curvatureSeedCanonicalChannelField
          (actualMetricPrincipalCoframeCandidateField4 g base)
          (positiveMaxwellMagnitudeFromSquare
            (actualRicciReconstructedQSqField4 g)) z))
      (pullCovectorToPrincipalFrame
        (actualMetricPrincipalCoframeCandidateField4 g base z)⁻¹
        (actualMetricScalarOneFormCandidateField4 g
          base.scalarTimelikeProbe base.scalarSpacelikeProbe
          base.relativeMinus z)) hactive
  refine ⟨channel, ?_⟩
  unfold IsActualMetricGenericFourthOrderComponentAt
  rw [actualMetricPrincipalCoframeCandidateField4_withChannel]
  exact ⟨hsource, hwedge⟩

/-- Exact finite-enumeration characterization of the intrinsic generic
locus. -/
theorem exists_actualMetricGenericFourthOrderComponentAt_withChannel_iff
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4) :
    (∃ channel : FourthOrderComponentChoice,
      IsActualMetricGenericFourthOrderComponentAt
        g z (base.withChannel channel)) ↔
      IsActualMetricActiveFourthOrderWedgeAt g z base := by
  constructor
  · rintro ⟨channel, hgeneric⟩
    unfold IsActualMetricGenericFourthOrderComponentAt at hgeneric
    unfold IsActualMetricActiveFourthOrderWedgeAt
    dsimp only
    rw [actualMetricPrincipalCoframeCandidateField4_withChannel] at hgeneric
    exact ⟨channel.2.1, channel.2.2, hgeneric.2⟩
  · exact exists_actualMetricGenericFourthOrderComponentAt_withChannel g z base

/-- The active-wedge predicate ignores the stored source/wedge indices. -/
@[simp] theorem isActualMetricActiveFourthOrderWedgeAt_withChannel
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (channel : FourthOrderComponentChoice) :
    IsActualMetricActiveFourthOrderWedgeAt g z (base.withChannel channel) ↔
      IsActualMetricActiveFourthOrderWedgeAt g z base := by
  rfl

/-- A physical channel plus the explicit finite generic component conditions
is enough for complete actual-metric acceptance.  This form cleanly separates
the genuine physical splice from the optional choice-indexed EMD witness. -/
theorem isActualMetricFourthOrderDetectorCandidateAt_of_upstream_physical
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
      g z choice a)
    (hgeneric : IsActualMetricGenericFourthOrderComponentAt
      g z choice) :
    IsActualMetricFourthOrderDetectorCandidateAt g z choice := by
  rcases hgeneric with ⟨hvsource, hnondegenerate⟩
  have hq := IsActualMetricUpstreamEntranceAt4.qPos
    g z choice hupstream
  refine ⟨hupstream, ?_⟩
  unfold IsCurvatureSeedFourthOrderCandidateAt
    IsTransportedSeedFourthOrderCandidate
  unfold IsActualMetricPhysicalConstantCouplingChannelAt at hphysical
  dsimp only at hphysical
  unfold curvatureSeedCanonicalChannelField at hphysical
  exact isFourthOrderChannelCandidate_of_physical
    (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) z))
    (pullCovectorToPrincipalFrame
      (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus z))
    (pullCovectorToPrincipalFrame
      (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
      (curvatureSeedCosineCoordinateDerivative
        (actualMetricPrincipalCoframeCandidateField4 g choice)
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g))
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus) choice.channel.1 z))
    (transportedPositiveQCanonicalSeedChannels
      (actualMetricPrincipalCoframeCandidateField4 g choice z)
      (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
      (matrixFieldCoordinateFDeriv4
        (actualMetricPrincipalCoframeCandidateField4 g choice) z)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z)
      (scalarFieldCoordinateFDeriv
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z))
    a choice.channel.1 choice.channel.2.1 choice.channel.2.2
    (Real.sqrt_ne_zero'.mpr (mul_pos (by norm_num) hq))
    hvsource hphysical hnondegenerate

/-- Direct accepted-set membership from the actual physical channel. -/
theorem mem_acceptedActualMetricFourthOrderDetectorChoicesAt_of_upstream_physical
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
      g z choice a)
    (hgeneric : IsActualMetricGenericFourthOrderComponentAt g z choice) :
    choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z := by
  rw [mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff]
  exact isActualMetricFourthOrderDetectorCandidateAt_of_upstream_physical
    g z choice a hupstream hphysical hgeneric

/-- **Actual-metric generic acceptance from the isolated entrance gate.**
Once one finite scalar/frame/Hodge choice passes the upstream metric-only
tests, a genuine EMD realization and the two displayed generic component
conditions force that same raw choice through the complete fourth-order
channel gate.  Thus the remaining necessity problem is precisely upstream
probe/entrance existence, not the coupling channel. -/
theorem isActualMetricFourthOrderDetectorCandidateAt_of_upstream_emdRealization
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hEMD : IsActualMetricConstantCouplingEMDRealizationAt
      g z choice a)
    (hgeneric : IsActualMetricGenericFourthOrderComponentAt
      g z choice) :
    IsActualMetricFourthOrderDetectorCandidateAt g z choice := by
  rcases hgeneric with ⟨hvsource, hnondegenerate⟩
  have hq := IsActualMetricUpstreamEntranceAt4.qPos
    g z choice hupstream
  refine ⟨hupstream, ?_⟩
  unfold IsCurvatureSeedFourthOrderCandidateAt
    IsTransportedSeedFourthOrderCandidate
  have hphysical :=
    isActualMetricPhysicalConstantCouplingChannelAt_of_emdRealization
      g z choice a hEMD
  unfold IsActualMetricPhysicalConstantCouplingChannelAt at hphysical
  dsimp only at hphysical
  unfold curvatureSeedCanonicalChannelField at hphysical
  exact isFourthOrderChannelCandidate_of_physical
    (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) z))
    (pullCovectorToPrincipalFrame
      (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus z))
    (pullCovectorToPrincipalFrame
      (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
      (curvatureSeedCosineCoordinateDerivative
        (actualMetricPrincipalCoframeCandidateField4 g choice)
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g))
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus) choice.channel.1 z))
    (transportedPositiveQCanonicalSeedChannels
      (actualMetricPrincipalCoframeCandidateField4 g choice z)
      (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
      (matrixFieldCoordinateFDeriv4
        (actualMetricPrincipalCoframeCandidateField4 g choice) z)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z)
      (scalarFieldCoordinateFDeriv
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z))
    a choice.channel.1 choice.channel.2.1 choice.channel.2.2
    (Real.sqrt_ne_zero'.mpr (mul_pos (by norm_num) hq))
    hvsource hphysical hnondegenerate

/-- **Metric-detector physical correctness.** Every accepted finite
metric-only branch that is the channel of a genuine constant-coupling
solution returns exactly `a²`.  No matter field or coupling enters the
detector definition itself. -/
theorem actualMetricFourthOrderCouplingSqCandidate_eq_physical
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hchoice : IsActualMetricFourthOrderDetectorCandidateAt g z choice)
    (hphysical :
      IsActualMetricPhysicalConstantCouplingChannelAt g z choice a) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice = a ^ 2 := by
  have hs := hchoice.toCurvatureSeed
  unfold IsCurvatureSeedFourthOrderCandidateAt
    IsTransportedSeedFourthOrderCandidate at hs
  unfold IsActualMetricPhysicalConstantCouplingChannelAt at hphysical
  unfold actualMetricFourthOrderCouplingSqCandidateAt
    curvatureSeedFourthOrderCouplingSqCandidateAt
    transportedSeedFourthOrderCouplingSqCandidate
  exact fourthOrderCouplingSqCandidate_eq_physical_of_acceptance
    _ _ _ _ _ _ hs hphysical

/-- **Nonvacuous actual-metric nonemptiness composition.** An upstream
metric choice, the intrinsic active wedge, and physical-channel correctness
for the finitely selected generic channel construct a genuine detector
survivor. The oriented signed coupling may be `a` or `-a`; only its square is
the geometric output. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_activeWedge
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z base)
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z base)
    (hphysical : ∀ channel : FourthOrderComponentChoice,
      IsActualMetricGenericFourthOrderComponentAt
          g z (base.withChannel channel) →
        ∃ orientedA : ℝ, orientedA ^ 2 = a ^ 2 ∧
          IsActualMetricPhysicalConstantCouplingChannelAt
            g z (base.withChannel channel) orientedA) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z choice = a ^ 2 := by
  obtain ⟨channel, hgeneric⟩ :=
    exists_actualMetricGenericFourthOrderComponentAt_withChannel
      g z base hactive
  obtain ⟨orientedA, horiented, hchannel⟩ :=
    hphysical channel hgeneric
  let choice := base.withChannel channel
  have hupstream' : IsActualMetricUpstreamEntranceAt4 g z choice :=
    (isActualMetricUpstreamEntranceAt4_withChannel
      g z base channel).mpr hupstream
  have haccepted :
      IsActualMetricFourthOrderDetectorCandidateAt g z choice :=
    isActualMetricFourthOrderDetectorCandidateAt_of_upstream_physical
      g z choice orientedA hupstream' hchannel hgeneric
  refine ⟨choice, ?_, ?_⟩
  · rw [mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff]
    exact haccepted
  · rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical
      g z choice orientedA haccepted hchannel, horiented]

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
/-- Kaluza specialization of the nonvacuous active-wedge composition. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_activeWedge
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z base)
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z base)
    (hphysical : ∀ channel : FourthOrderComponentChoice,
      IsActualMetricGenericFourthOrderComponentAt
          g z (base.withChannel channel) →
        ∃ orientedA : ℝ, orientedA ^ 2 = a ^ 2 ∧
          IsActualMetricPhysicalConstantCouplingChannelAt
            g z (base.withChannel channel) orientedA)
    (hKaluza : a ^ 2 = 3) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z choice = 3 := by
  obtain ⟨choice, hmem, hout⟩ :=
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_activeWedge
      g z base a hupstream hactive hphysical
  exact ⟨choice, hmem, hout.trans hKaluza⟩

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

/-- **Metric-only EMD necessity/result theorem.** Every accepted finite raw
metric branch admitting a genuine constant-coupling EMD realization returns
the physical invariant `a²`, without separately assuming the packaged
physical-channel predicate. -/
theorem actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_emdRealization
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hchoice : IsActualMetricFourthOrderDetectorCandidateAt g z choice)
    (hEMD : IsActualMetricConstantCouplingEMDRealizationAt
      g z choice a) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice = a ^ 2 := by
  exact actualMetricFourthOrderCouplingSqCandidate_eq_physical
    g z choice a hchoice
    (isActualMetricPhysicalConstantCouplingChannelAt_of_emdRealization
      g z choice a hEMD)

/-- The isolated upstream entrance, genuine EMD realization, and generic
component condition construct an actual member of the finite metric-only
accepted set. -/
theorem mem_acceptedActualMetricFourthOrderDetectorChoicesAt_of_upstream_emdRealization
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hEMD : IsActualMetricConstantCouplingEMDRealizationAt
      g z choice a)
    (hgeneric : IsActualMetricGenericFourthOrderComponentAt
      g z choice) :
    choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z := by
  rw [mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff]
  exact
    isActualMetricFourthOrderDetectorCandidateAt_of_upstream_emdRealization
      g z choice a hupstream hEMD hgeneric

/-- **Conditional north-star detector theorem at the actual metric
boundary.**  On the explicit upstream chart branch, genuine EMD realization
and the generic fourth-order component condition both construct acceptance
and force the metric-only output to be `a²`. -/
theorem actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_upstream_emdRealization
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hEMD : IsActualMetricConstantCouplingEMDRealizationAt
      g z choice a)
    (hgeneric : IsActualMetricGenericFourthOrderComponentAt
      g z choice) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice = a ^ 2 := by
  exact actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_emdRealization
    g z choice a
    (isActualMetricFourthOrderDetectorCandidateAt_of_upstream_emdRealization
      g z choice a hupstream hEMD hgeneric)
    hEMD

/-- On the same explicit upstream branch, the Kaluza coupling is selected by
the metric-only value `3`. -/
theorem actualMetricFourthOrderCouplingSqCandidate_eq_three_of_upstream_emdRealization
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hEMD : IsActualMetricConstantCouplingEMDRealizationAt
      g z choice a)
    (hgeneric : IsActualMetricGenericFourthOrderComponentAt
      g z choice)
    (hKaluza : a ^ 2 = 3) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice = 3 := by
  rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_upstream_emdRealization
    g z choice a hupstream hEMD hgeneric, hKaluza]

/-- A genuine Kaluza-coupling EMD realization makes every accepted metric
branch return the distinguished selector value `3`. -/
theorem actualMetricFourthOrderCouplingSqCandidate_eq_three_of_emdRealization
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hchoice : IsActualMetricFourthOrderDetectorCandidateAt g z choice)
    (hEMD : IsActualMetricConstantCouplingEMDRealizationAt
      g z choice a)
    (hKaluza : a ^ 2 = 3) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice = 3 := by
  rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_emdRealization
    g z choice a hchoice hEMD, hKaluza]

/-- **Kaluza selector at the metric-only boundary.** On a genuine generic
Kaluza-reduced channel, whose fixed EMD coupling obeys `a²=3`, every accepted
raw choice returns the distinguished value `3`. -/
theorem actualMetricFourthOrderCouplingSqCandidate_eq_three
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hchoice : IsActualMetricFourthOrderDetectorCandidateAt g z choice)
    (hphysical :
      IsActualMetricPhysicalConstantCouplingChannelAt g z choice a)
    (hKaluza : a ^ 2 = 3) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice = 3 := by
  rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical
    g z choice a hchoice hphysical, hKaluza]

/-- **Full raw-choice confluence on genuine physical data.** Two accepted
metric-only choices compatible with the same physical constant coupling have
equal outputs, regardless of their scalar relative-sign, scalar probes,
principal-frame probes, Hodge orientation branch, or quotient components. -/
theorem actualMetricFourthOrderCouplingSqCandidates_eq_of_physicalAcceptance
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice choice' : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hchoice : IsActualMetricFourthOrderDetectorCandidateAt g z choice)
    (hchoice' : IsActualMetricFourthOrderDetectorCandidateAt g z choice')
    (hphysical :
      IsActualMetricPhysicalConstantCouplingChannelAt g z choice a)
    (hphysical' :
      IsActualMetricPhysicalConstantCouplingChannelAt g z choice' a) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      actualMetricFourthOrderCouplingSqCandidateAt g z choice' := by
  rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical
      g z choice a hchoice hphysical,
    actualMetricFourthOrderCouplingSqCandidate_eq_physical
      g z choice' a hchoice' hphysical']

/-- **Metric-only channel-choice confluence.** Once the finite scalar branch
and principal-frame probes are fixed, every channel/source/wedge choice that
survives throughout an open positive-square patch returns the same squared
coupling.  This lifts the source-component and next-order quotient
independence theorem all the way to the finite metric-only detector. -/
theorem actualMetricFourthOrderCouplingSqCandidates_eq_of_channelAcceptance
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (channel channel' : FourthOrderComponentChoice)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hqSqPos : ∀ y ∈ U, 0 < actualRicciReconstructedQSqField4 g y)
    (hchoice : ∀ y ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g y
        (base.withChannel channel))
    (hchoice' : ∀ y ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g y
        (base.withChannel channel')) :
    actualMetricFourthOrderCouplingSqCandidateAt g z
        (base.withChannel channel) =
      actualMetricFourthOrderCouplingSqCandidateAt g z
        (base.withChannel channel') := by
  change curvatureSeedFourthOrderCouplingSqCandidateAt
      (actualMetricPrincipalCoframeCandidateField4 g base)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (actualMetricScalarOneFormCandidateField4 g
        base.scalarTimelikeProbe base.scalarSpacelikeProbe
        base.relativeMinus)
      z channel =
    curvatureSeedFourthOrderCouplingSqCandidateAt
      (actualMetricPrincipalCoframeCandidateField4 g base)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (actualMetricScalarOneFormCandidateField4 g
        base.scalarTimelikeProbe base.scalarSpacelikeProbe
        base.relativeMinus)
      z channel'
  apply curvatureSeedFourthOrderCouplingSqCandidates_eq_of_patchAcceptance
    (actualMetricPrincipalCoframeCandidateField4 g base)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g))
    (actualMetricScalarOneFormCandidateField4 g
      base.scalarTimelikeProbe base.scalarSpacelikeProbe base.relativeMinus)
    channel channel' z hopen hz
  · intro y hy
    exact positiveMaxwellMagnitudeFromSquare_pos _ _ (hqSqPos y hy)
  · intro y hy
    have hs := (hchoice y hy).toCurvatureSeed
    rw [actualMetricPrincipalCoframeCandidateField4_withChannel] at hs
    change IsCurvatureSeedFourthOrderCandidateAt
      (actualMetricPrincipalCoframeCandidateField4 g base)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (actualMetricScalarOneFormCandidateField4 g
        base.scalarTimelikeProbe base.scalarSpacelikeProbe
        base.relativeMinus) y channel at hs
    exact hs
  · intro y hy
    have hs := (hchoice' y hy).toCurvatureSeed
    rw [actualMetricPrincipalCoframeCandidateField4_withChannel] at hs
    change IsCurvatureSeedFourthOrderCandidateAt
      (actualMetricPrincipalCoframeCandidateField4 g base)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (actualMetricScalarOneFormCandidateField4 g
        base.scalarTimelikeProbe base.scalarSpacelikeProbe
        base.relativeMinus) y channel' at hs
    exact hs

end RainichKaluza
