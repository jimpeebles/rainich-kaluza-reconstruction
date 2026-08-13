import RainichKaluza.FourthOrderMetricDetector
import RainichKaluza.PhysicalScalarIdentifiability

/-!
# Actual-metric scalar identifiability

This file instantiates the abstract physical scalar entrance theorem at the
polynomial projectors and finite coordinate probes used by the metric-only
detector.  It is deliberately separate from the detector implementation: the
physical covector occurs only in the correctness hypothesis and is not an
input to the finite metric construction.
-/

namespace RainichKaluza

open scoped Topology
open LinearMap (BilinForm)
open Module

/-- A continuous nonzero covector branch cannot switch between a field and
its negative arbitrarily close to a point where its sign is fixed.  This is
the local topological mechanism needed to promote pointwise scalar
identifiability to first-jet identifiability. -/
theorem eventuallyEq_of_continuousAt_eq_or_neg
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f v : X → E} {z : X}
    (hf : ContinuousAt f z) (hv : ContinuousAt v z)
    (hv0 : v z ≠ 0) (hz : f z = v z)
    (horbit : ∀ᶠ y in 𝓝 z, f y = v y ∨ f y = -v y) :
    f =ᶠ[𝓝 z] v := by
  have hvneg : v z ≠ -v z := by
    intro h
    have htwo : (2 : ℝ) • v z = 0 := by
      rw [two_smul]
      calc
        v z + v z = v z + (-v z) := by rw [← h]
        _ = 0 := add_neg_cancel (v z)
    exact hv0 ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
  have hsep : dist (f z) (v z) < dist (f z) (-v z) := by
    rw [hz, dist_self]
    exact dist_pos.mpr hvneg
  have hlt := (hf.dist hv).eventually_lt (hf.dist hv.neg) hsep
  filter_upwards [horbit, hlt] with y hy hylt
  rcases hy with hy | hy
  · exact hy
  · exfalso
    rw [hy] at hylt
    have : dist (-v y) (v y) < 0 := by simpa using hylt
    exact (not_lt_of_ge dist_nonneg) this

/-- Consequently an eventually pointwise `±`-identified continuous nonzero
branch has one constant sign on a smaller neighborhood. -/
theorem eventuallyEq_or_eventuallyEq_neg_of_continuousAt_orbit
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f v : X → E} {z : X}
    (hf : ContinuousAt f z) (hv : ContinuousAt v z)
    (hv0 : v z ≠ 0)
    (horbit : ∀ᶠ y in 𝓝 z, f y = v y ∨ f y = -v y) :
    f =ᶠ[𝓝 z] v ∨ f =ᶠ[𝓝 z] fun y => -v y := by
  have hz := horbit.self_of_nhds
  rcases hz with hz | hz
  · exact Or.inl
      (eventuallyEq_of_continuousAt_eq_or_neg hf hv hv0 hz horbit)
  · apply Or.inr
    have horbitNeg : ∀ᶠ y in 𝓝 z,
        f y = (-v) y ∨ f y = -(-v) y := by
      filter_upwards [horbit] with y hy
      rcases hy with hy | hy
      · exact Or.inr (by simpa using hy)
      · exact Or.inl (by simpa using hy)
    exact eventuallyEq_of_continuousAt_eq_or_neg hf hv.neg
      (by simpa using hv0) (by simpa using hz) horbitNeg

/-- A scalar-orientation germ reverses the detector's literal quotient field,
so its actual coordinate Frechet derivative reverses automatically.  No
independent derivative-sign hypothesis is needed. -/
theorem curvatureSeedCosineCoordinateDerivative_eq_neg_of_scalarGerm
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (detectorV physicalV : CurvatureCoordinateSpace4 → OneForm4)
    (source : Fin 4) (z : CurvatureCoordinateSpace4)
    (hscalar : detectorV =ᶠ[nhds z] fun y ↦ -physicalV y) :
    curvatureSeedCosineCoordinateDerivative L q detectorV source z =
      -curvatureSeedCosineCoordinateDerivative L q physicalV source z := by
  have hcosine : curvatureSeedCosineField L q detectorV source =ᶠ[nhds z]
      fun y ↦ -curvatureSeedCosineField L q physicalV source y := by
    filter_upwards [hscalar] with y hy
    unfold curvatureSeedCosineField
    rw [hy]
    have hpull :
        pullCovectorToPrincipalFrame (L y)⁻¹ (-physicalV y) =
          -pullCovectorToPrincipalFrame (L y)⁻¹ (physicalV y) := by
      simpa only [neg_one_smul] using
        pullCovectorToPrincipalFrame_smul (L y)⁻¹ (-1) (physicalV y)
    rw [hpull, canonicalCosineCandidateFromChannels_neg_scalar]
  unfold curvatureSeedCosineCoordinateDerivative
    scalarFieldCoordinateFDeriv
  rw [Filter.EventuallyEq.fderiv_eq hcosine, fderiv_fun_neg]
  rfl

/-- Scalar-orientation covariance with the detector derivative reconstructed
from an actual field germ.  The existing algebraic physical-channel symmetry
then changes `a` to `-a`. -/
theorem isPhysicalConstantCouplingChannel_of_neg_scalarGerm
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (detectorV physicalV : CurvatureCoordinateSpace4 → OneForm4)
    (E : ℝ) (K : Matrix4) (X : ThreeTensor4 × ThreeTensor4)
    (a : ℝ) (source : Fin 4) (z : CurvatureCoordinateSpace4)
    (hscalar : detectorV =ᶠ[nhds z] fun y ↦ -physicalV y)
    (hphysical : IsPhysicalConstantCouplingChannel E
      (pullCovectorToPrincipalFrame K (physicalV z))
      (pullCovectorToPrincipalFrame K
        (curvatureSeedCosineCoordinateDerivative
          L q physicalV source z)) X a) :
    IsPhysicalConstantCouplingChannel E
      (pullCovectorToPrincipalFrame K (detectorV z))
      (pullCovectorToPrincipalFrame K
        (curvatureSeedCosineCoordinateDerivative
          L q detectorV source z)) X (-a) := by
  have hv : pullCovectorToPrincipalFrame K (detectorV z) =
      -pullCovectorToPrincipalFrame K (physicalV z) := by
    rw [hscalar.self_of_nhds]
    simpa only [neg_one_smul] using
      pullCovectorToPrincipalFrame_smul K (-1) (physicalV z)
  have hdA : pullCovectorToPrincipalFrame K
        (curvatureSeedCosineCoordinateDerivative L q detectorV source z) =
      -pullCovectorToPrincipalFrame K
        (curvatureSeedCosineCoordinateDerivative L q physicalV source z) := by
    rw [curvatureSeedCosineCoordinateDerivative_eq_neg_of_scalarGerm
      L q detectorV physicalV source z hscalar]
    simpa only [neg_one_smul] using
      pullCovectorToPrincipalFrame_smul K (-1)
        (curvatureSeedCosineCoordinateDerivative L q physicalV source z)
  rw [hv, hdA]
  exact (isPhysicalConstantCouplingChannel_neg_scalar E
    (pullCovectorToPrincipalFrame K (physicalV z))
    (pullCovectorToPrincipalFrame K
      (curvatureSeedCosineCoordinateDerivative L q physicalV source z))
    X a).mpr hphysical

/-- Pointwise exterior EMD closure has the same scalar-sign covariance: a
physical closure for `(v,a)` is a detector closure for `(-v,-a)`. -/
theorem emdExteriorClosure_detectorScalar_neg_physical
    (detectorV physicalV : OneForm4) (a : ℝ)
    (F G : Matrix4) (dF dG : ThreeTensor4)
    (hscalar : detectorV = -physicalV)
    (hclosure : EMDExteriorClosure matrixOneWedgeTwo physicalV a
      F G dF dG) :
    EMDExteriorClosure matrixOneWedgeTwo detectorV (-a) F G dF dG := by
  rw [hscalar]
  exact (emdExteriorClosure_neg_scalar_coupling
    matrixOneWedgeTwo physicalV a F G dF dG).mpr hclosure

/-- **Negative scalar-germ physical-channel splice.**  If the detector
scalar germ is the negative of the physical scalar germ, a neighborhood
physical seed-channel identity with coupling `a` yields the detector's full
physical-channel predicate with coupling `-a`.  The quotient derivative sign
is a theorem of the germ, rather than a separately supplied premise. -/
theorem isPhysicalConstantCouplingChannel_of_neg_scalar_physicalSeedChannelGerm
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (detectorV physicalV omega : CurvatureCoordinateSpace4 → OneForm4)
    (a : ℝ) (c s : CurvatureCoordinateSpace4 → ℝ)
    (source : Fin 4) (z : CurvatureCoordinateSpace4)
    (hscalar : detectorV =ᶠ[nhds z] fun y ↦ -physicalV y)
    (hq : ∀ᶠ y in nhds z, 0 < q y)
    (hsource : ∀ᶠ y in nhds z,
      pullCovectorToPrincipalFrame (L y)⁻¹ (physicalV y) source ≠ 0)
    (hchannels : ∀ᶠ y in nhds z,
      curvatureSeedCanonicalChannelField L q y =
        canonicalPhysicalSeedChannels (Real.sqrt (2 * q y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (physicalV y))
          (pullCovectorToPrincipalFrame (L y)⁻¹ (omega y))
          (a * (c y ^ 2 - s y ^ 2)) (a * (2 * c y * s y)))
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z)
    (hunit : c z ^ 2 + s z ^ 2 = 1)
    (hdc : scalarFieldCoordinateFDeriv c z = (-s z) • omega z)
    (hds : scalarFieldCoordinateFDeriv s z = c z • omega z) :
    IsPhysicalConstantCouplingChannel (Real.sqrt (2 * q z))
      (pullCovectorToPrincipalFrame (L z)⁻¹ (detectorV z))
      (pullCovectorToPrincipalFrame (L z)⁻¹
        (curvatureSeedCosineCoordinateDerivative
          L q detectorV source z))
      (curvatureSeedCanonicalChannelField L q z) (-a) := by
  have hphysical :=
    isPhysicalConstantCouplingChannel_of_physicalSeedChannelGerm
      L q physicalV omega a c s source z hq hsource hchannels
        hc hs hunit hdc hds
  exact isPhysicalConstantCouplingChannel_of_neg_scalarGerm
    L q detectorV physicalV (Real.sqrt (2 * q z)) (L z)⁻¹
    (curvatureSeedCanonicalChannelField L q z) a source z
    hscalar hphysical

/-- If two continuous reconstructed branches jointly cover the physical
`±`-orbit near a point, and the second branch is not in that orbit at the
base point, then the first branch alone covers it on a smaller neighborhood.

This is the finite-branch separation step: it turns pointwise existence of
one of two relative-sign choices into one fixed local choice. -/
theorem eventually_orbit_of_continuous_two_branch_cover
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p m v : X → E} {z : X}
    (hm : ContinuousAt m z)
    (hv : ContinuousAt v z)
    (hcover : ∀ᶠ y in 𝓝 z,
      (p y = v y ∨ p y = -v y) ∨
        (m y = v y ∨ m y = -v y))
    (hmPlus : m z ≠ v z) (hmMinus : m z ≠ -v z) :
    ∀ᶠ y in 𝓝 z, p y = v y ∨ p y = -v y := by
  have hmPlusEventually : ∀ᶠ y in 𝓝 z, m y ≠ v y :=
    (hm.ne_iff_eventually_ne hv).mp hmPlus
  have hmMinusEventually : ∀ᶠ y in 𝓝 z, m y ≠ -v y :=
    (hm.ne_iff_eventually_ne hv.neg).mp hmMinus
  filter_upwards [hcover, hmPlusEventually, hmMinusEventually]
      with y hy hnePlus hneMinus
  rcases hy with hpOrbit | hmOrbit
  · exact hpOrbit
  · exact False.elim (hmOrbit.elim hnePlus hneMinus)

/-- With both spectral components nonzero, the sum and difference branches
cannot both represent the same covector up to overall sign. -/
theorem sub_not_in_orbit_of_add_in_orbit
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {alpha beta v : E} (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hadd : alpha + beta = v ∨ alpha + beta = -v) :
    alpha - beta ≠ v ∧ alpha - beta ≠ -v := by
  constructor <;> intro hsub <;> rcases hadd with hadd | hadd
  · apply hbeta
    have htwo : (2 : ℝ) • beta = 0 := by
      rw [two_smul]
      calc
        beta + beta = (alpha + beta) - (alpha - beta) := by abel
        _ = v - v := by rw [hadd, hsub]
        _ = 0 := sub_self v
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · apply halpha
    have htwo : (2 : ℝ) • alpha = 0 := by
      rw [two_smul]
      calc
        alpha + alpha = (alpha + beta) + (alpha - beta) := by abel
        _ = -v + v := by rw [hadd, hsub]
        _ = 0 := neg_add_cancel v
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · apply halpha
    have htwo : (2 : ℝ) • alpha = 0 := by
      rw [two_smul]
      calc
        alpha + alpha = (alpha + beta) + (alpha - beta) := by abel
        _ = v + -v := by rw [hadd, hsub]
        _ = 0 := add_neg_cancel v
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · apply hbeta
    have htwo : (2 : ℝ) • beta = 0 := by
      rw [two_smul]
      calc
        beta + beta = (alpha + beta) - (alpha - beta) := by abel
        _ = -v - -v := by rw [hadd, hsub]
        _ = 0 := sub_self (-v)
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Symmetric form of the preceding separation lemma. -/
theorem add_not_in_orbit_of_sub_in_orbit
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {alpha beta v : E} (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hsub : alpha - beta = v ∨ alpha - beta = -v) :
    alpha + beta ≠ v ∧ alpha + beta ≠ -v := by
  constructor <;> intro hadd <;> rcases hsub with hsub | hsub
  · apply hbeta
    have htwo : (2 : ℝ) • beta = 0 := by
      rw [two_smul]
      calc
        beta + beta = (alpha + beta) - (alpha - beta) := by abel
        _ = v - v := by rw [hadd, hsub]
        _ = 0 := sub_self v
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · apply halpha
    have htwo : (2 : ℝ) • alpha = 0 := by
      rw [two_smul]
      calc
        alpha + alpha = (alpha + beta) + (alpha - beta) := by abel
        _ = v + -v := by rw [hadd, hsub]
        _ = 0 := add_neg_cancel v
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · apply halpha
    have htwo : (2 : ℝ) • alpha = 0 := by
      rw [two_smul]
      calc
        alpha + alpha = (alpha + beta) + (alpha - beta) := by abel
        _ = -v + v := by rw [hadd, hsub]
        _ = 0 := neg_add_cancel v
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · apply hbeta
    have htwo : (2 : ℝ) • beta = 0 := by
      rw [two_smul]
      calc
        beta + beta = (alpha + beta) - (alpha - beta) := by abel
        _ = -v - -v := by rw [hadd, hsub]
        _ = 0 := sub_self (-v)
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Eventual identification of the realized sum branch with a closed physical
scalar field forces the displayed curvature closure obstruction to vanish at
the base point. -/
theorem RealizedCurvatureScalarBranchPatch4.plusObstruction_eq_zero_of_eventuallyEq_closed
    {U : Set CurvatureCoordinateSpace4}
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hclosed : IsClosedScalarOneFormOn v U)
    (heq : B.plusField =ᶠ[𝓝 z] v) :
    (B.jet z).dalpha + (B.jet z).dbeta = 0 := by
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq
  have hsymm : ∀ u w,
      oneFormJetEvaluate (B.jet z).vPlusJet u w =
        oneFormJetEvaluate (B.jet z).vPlusJet w u := by
    intro u w
    calc
      oneFormJetEvaluate (B.jet z).vPlusJet u w =
          fderiv ℝ B.plusField z u w :=
        (B.plusField_fderiv hopen z hz u w).symm
      _ = fderiv ℝ v z u w := by rw [hfd]
      _ = fderiv ℝ v z w u := hclosed.2 z hz u w
      _ = fderiv ℝ B.plusField z w u := by rw [hfd]
      _ = oneFormJetEvaluate (B.jet z).vPlusJet w u :=
        B.plusField_fderiv hopen z hz w u
  have hext := (oneFormJetEvaluate_symmetric_iff
    (B.jet z).vPlusJet).mp hsymm
  rwa [(B.jet z).vPlus_exterior] at hext

/-- The corresponding statement for the realized difference branch. -/
theorem RealizedCurvatureScalarBranchPatch4.minusObstruction_eq_zero_of_eventuallyEq_closed
    {U : Set CurvatureCoordinateSpace4}
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hclosed : IsClosedScalarOneFormOn v U)
    (heq : B.minusField =ᶠ[𝓝 z] v) :
    (B.jet z).dalpha - (B.jet z).dbeta = 0 := by
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq
  have hsymm : ∀ u w,
      oneFormJetEvaluate (B.jet z).vMinusJet u w =
        oneFormJetEvaluate (B.jet z).vMinusJet w u := by
    intro u w
    calc
      oneFormJetEvaluate (B.jet z).vMinusJet u w =
          fderiv ℝ B.minusField z u w :=
        (B.minusField_fderiv hopen z hz u w).symm
      _ = fderiv ℝ v z u w := by rw [hfd]
      _ = fderiv ℝ v z w u := hclosed.2 z hz u w
      _ = fderiv ℝ B.minusField z w u := by rw [hfd]
      _ = oneFormJetEvaluate (B.jet z).vMinusJet w u :=
        B.minusField_fderiv hopen z hz w u
  have hext := (oneFormJetEvaluate_symmetric_iff
    (B.jet z).vMinusJet).mp hsymm
  rwa [(B.jet z).vMinus_exterior] at hext

/-- **Fixed local branch/first-jet identifiability.**  Suppose the two
realized metric branches jointly cover the physical scalar covector up to
sign throughout a neighborhood.  If the physical scalar and both spectral
components are nonzero at the base point, one fixed branch agrees with one
fixed global sign on a smaller neighborhood.  Hence its literal displayed
curvature closure obstruction vanishes.

This theorem is the precise bridge from pointwise algebraic identifiability
to the fourth-order detector's first-jet gate. -/
theorem RealizedCurvatureScalarBranchPatch4.exists_branchObstruction_eq_zero_of_local_orbit
    {U : Set CurvatureCoordinateSpace4}
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : ContinuousAt v z) (hv0 : v z ≠ 0)
    (hclosed : IsClosedScalarOneFormOn v U)
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hcover : ∀ᶠ y in 𝓝 z,
      (B.plusField y = v y ∨ B.plusField y = -v y) ∨
        (B.minusField y = v y ∨ B.minusField y = -v y)) :
    (B.jet z).dalpha + (B.jet z).dbeta = 0 ∨
      (B.jet z).dalpha - (B.jet z).dbeta = 0 := by
  have hplusContinuous : ContinuousAt B.plusField z :=
    ((B.plusField_differentiable z hz).differentiableAt
      (hopen.mem_nhds hz)).continuousAt
  have hminusContinuous : ContinuousAt B.minusField z :=
    ((B.minusField_differentiable z hz).differentiableAt
      (hopen.mem_nhds hz)).continuousAt
  have hclosedNeg : IsClosedScalarOneFormOn (fun y => -v y) U := by
    constructor
    · exact hclosed.1.neg
    · intro y hy u w
      change fderiv ℝ (-v) y u w = fderiv ℝ (-v) y w u
      rw [fderiv_neg]
      simp only [neg_apply]
      rw [hclosed.2 y hy u w]
  rcases hcover.self_of_nhds with hplusOrbit | hminusOrbit
  · have hsep : B.minusField z ≠ v z ∧ B.minusField z ≠ -v z := by
      have hsep' := sub_not_in_orbit_of_add_in_orbit
        halpha hbeta (by
          simpa [RealizedCurvatureScalarBranchPatch4.plusField] using
            hplusOrbit)
      simpa [RealizedCurvatureScalarBranchPatch4.minusField] using hsep'
    have hplusCover := eventually_orbit_of_continuous_two_branch_cover
      hminusContinuous hv hcover hsep.1 hsep.2
    rcases eventuallyEq_or_eventuallyEq_neg_of_continuousAt_orbit
        hplusContinuous hv hv0 hplusCover with hEq | hEq
    · exact Or.inl
        (B.plusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz v hclosed hEq)
    · exact Or.inl
        (B.plusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz (fun y => -v y) hclosedNeg hEq)
  · have hsep : B.plusField z ≠ v z ∧ B.plusField z ≠ -v z := by
      have hsep' := add_not_in_orbit_of_sub_in_orbit
        halpha hbeta (by
          simpa [RealizedCurvatureScalarBranchPatch4.minusField] using
            hminusOrbit)
      simpa [RealizedCurvatureScalarBranchPatch4.plusField] using hsep'
    have hcoverSwap : ∀ᶠ y in 𝓝 z,
        (B.minusField y = v y ∨ B.minusField y = -v y) ∨
          (B.plusField y = v y ∨ B.plusField y = -v y) := by
      filter_upwards [hcover] with y hy
      exact hy.symm
    have hminusCover := eventually_orbit_of_continuous_two_branch_cover
      hplusContinuous hv hcoverSwap hsep.1 hsep.2
    rcases eventuallyEq_or_eventuallyEq_neg_of_continuousAt_orbit
        hminusContinuous hv hv0 hminusCover with hEq | hEq
    · exact Or.inr
        (B.minusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz v hclosed hEq)
    · exact Or.inr
        (B.minusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz (fun y => -v y) hclosedNeg hEq)

/-- Strengthened local branch theorem retaining the selected branch's whole
germ in one fixed physical sign orbit, together with its obstruction.  The
germ—not merely its base-point value—is what transfers the actual fourth-order
Frechet derivative into the physical EMD channel. -/
theorem RealizedCurvatureScalarBranchPatch4.exists_branchGerm_and_obstruction_eq_zero_of_local_orbit
    {U : Set CurvatureCoordinateSpace4}
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : ContinuousAt v z) (hv0 : v z ≠ 0)
    (hclosed : IsClosedScalarOneFormOn v U)
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hcover : ∀ᶠ y in 𝓝 z,
      (B.plusField y = v y ∨ B.plusField y = -v y) ∨
        (B.minusField y = v y ∨ B.minusField y = -v y)) :
    ((B.plusField =ᶠ[nhds z] v ∨
          B.plusField =ᶠ[nhds z] fun y => -v y) ∧
        (B.jet z).dalpha + (B.jet z).dbeta = 0) ∨
      ((B.minusField =ᶠ[nhds z] v ∨
          B.minusField =ᶠ[nhds z] fun y => -v y) ∧
        (B.jet z).dalpha - (B.jet z).dbeta = 0) := by
  have hplusContinuous : ContinuousAt B.plusField z :=
    ((B.plusField_differentiable z hz).differentiableAt
      (hopen.mem_nhds hz)).continuousAt
  have hminusContinuous : ContinuousAt B.minusField z :=
    ((B.minusField_differentiable z hz).differentiableAt
      (hopen.mem_nhds hz)).continuousAt
  have hclosedNeg : IsClosedScalarOneFormOn (fun y => -v y) U := by
    constructor
    · exact hclosed.1.neg
    · intro y hy u w
      change fderiv ℝ (-v) y u w = fderiv ℝ (-v) y w u
      rw [fderiv_neg]
      simp only [neg_apply]
      rw [hclosed.2 y hy u w]
  rcases hcover.self_of_nhds with hplusOrbit | hminusOrbit
  · have hsep : B.minusField z ≠ v z ∧ B.minusField z ≠ -v z := by
      have hsep' := sub_not_in_orbit_of_add_in_orbit
        halpha hbeta (by
          simpa [RealizedCurvatureScalarBranchPatch4.plusField] using
            hplusOrbit)
      simpa [RealizedCurvatureScalarBranchPatch4.minusField] using hsep'
    have hplusCover := eventually_orbit_of_continuous_two_branch_cover
      hminusContinuous hv hcover hsep.1 hsep.2
    rcases eventuallyEq_or_eventuallyEq_neg_of_continuousAt_orbit
        hplusContinuous hv hv0 hplusCover with hEq | hEq
    · exact Or.inl ⟨Or.inl hEq,
        B.plusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz v hclosed hEq⟩
    · exact Or.inl ⟨Or.inr hEq,
        B.plusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz (fun y => -v y) hclosedNeg hEq⟩
  · have hsep : B.plusField z ≠ v z ∧ B.plusField z ≠ -v z := by
      have hsep' := add_not_in_orbit_of_sub_in_orbit
        halpha hbeta (by
          simpa [RealizedCurvatureScalarBranchPatch4.minusField] using
            hminusOrbit)
      simpa [RealizedCurvatureScalarBranchPatch4.plusField] using hsep'
    have hcoverSwap : ∀ᶠ y in 𝓝 z,
        (B.minusField y = v y ∨ B.minusField y = -v y) ∨
          (B.plusField y = v y ∨ B.plusField y = -v y) := by
      filter_upwards [hcover] with y hy
      exact hy.symm
    have hminusCover := eventually_orbit_of_continuous_two_branch_cover
      hplusContinuous hv hcoverSwap hsep.1 hsep.2
    rcases eventuallyEq_or_eventuallyEq_neg_of_continuousAt_orbit
        hminusContinuous hv hv0 hminusCover with hEq | hEq
    · exact Or.inr ⟨Or.inl hEq,
        B.minusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz v hclosed hEq⟩
    · exact Or.inr ⟨Or.inr hEq,
        B.minusObstruction_eq_zero_of_eventuallyEq_closed
          hopen hz (fun y => -v y) hclosedNeg hEq⟩

/-- Base-point corollary of the germ-level selector, retained for downstream
pointwise algebra. -/
theorem RealizedCurvatureScalarBranchPatch4.exists_branchOrbit_and_obstruction_eq_zero_of_local_orbit
    {U : Set CurvatureCoordinateSpace4}
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : ContinuousAt v z) (hv0 : v z ≠ 0)
    (hclosed : IsClosedScalarOneFormOn v U)
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hcover : ∀ᶠ y in 𝓝 z,
      (B.plusField y = v y ∨ B.plusField y = -v y) ∨
        (B.minusField y = v y ∨ B.minusField y = -v y)) :
    ((B.plusField z = v z ∨ B.plusField z = -v z) ∧
        (B.jet z).dalpha + (B.jet z).dbeta = 0) ∨
      ((B.minusField z = v z ∨ B.minusField z = -v z) ∧
        (B.jet z).dalpha - (B.jet z).dbeta = 0) := by
  rcases B.exists_branchGerm_and_obstruction_eq_zero_of_local_orbit
      hopen hz v hv hv0 hclosed halpha hbeta hcover with hplus | hminus
  · exact Or.inl ⟨hplus.1.elim
      (fun h => Or.inl h.self_of_nhds)
      (fun h => Or.inr h.self_of_nhds), hplus.2⟩
  · exact Or.inr ⟨hminus.1.elim
      (fun h => Or.inl h.self_of_nhds)
      (fun h => Or.inr h.self_of_nhds), hminus.2⟩

/-- The coordinate directions enumerated by the detector are exactly the
ambient standard basis used by the finite-probe theorem. -/
theorem curvatureCoordinateDirection_eq_piBasisFun (i : Fin 4) :
    curvatureCoordinateDirection i = (Pi.basisFun ℝ (Fin 4)) i := by
  ext j
  simp [curvatureCoordinateDirection, Pi.basisFun_apply, Pi.single_apply]

@[simp] theorem oneForm4ContinuousLinearMap_add'
    (u v : OneForm4) :
    oneForm4ContinuousLinearMap (u + v) =
      oneForm4ContinuousLinearMap u + oneForm4ContinuousLinearMap v := by
  ext y
  simp only [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    Pi.add_apply, add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem oneForm4ContinuousLinearMap_sub'
    (u v : OneForm4) :
    oneForm4ContinuousLinearMap (u - v) =
      oneForm4ContinuousLinearMap u - oneForm4ContinuousLinearMap v := by
  ext y
  simp only [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    Pi.sub_apply, sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The stored actual-metric scalar candidate is definitionally the expanded
amplitude-weighted sum/difference of the two normalized polynomial-projector
eigen-one-forms.  This is the implementation bridge used to turn the
finite-probe existence theorem into a statement about the detector output. -/
theorem actualMetricScalarOneFormCandidate_toLinearMap
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (i j : Fin 4) (relativeMinus : Bool) :
    (oneForm4ContinuousLinearMap
      (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
      let gb := continuousBilinFormToBilin (g z)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g z)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g z)
      let u := (Pi.basisFun ℝ (Fin 4)) i
      let w := (Pi.basisFun ℝ (Fin 4)) j
      let ampA := Real.sqrt (2 * (-1 : ℝ) * reconstructedDiagonalA
        (actualRicciComplementaryRootAField4 g z)
        (actualRicciComplementaryRootBField4 g z)
        (actualRicciReconstructedQSqField4 g z))
      let ampB := Real.sqrt (2 * (1 : ℝ) * reconstructedDiagonalB
        (actualRicciComplementaryRootAField4 g z)
        (actualRicciComplementaryRootBField4 g z)
        (actualRicciReconstructedQSqField4 g z))
      if relativeMinus then
        ampA • gb (normalizeTimelike gb (P u)) -
          ampB • gb (normalizeSpacelike gb (Q w))
      else
        ampA • gb (normalizeTimelike gb (P u)) +
          ampB • gb (normalizeSpacelike gb (Q w)) := by
  simp only [actualMetricScalarOneFormCandidateField4,
    actualMetricScalarBranchJetField4,
    concreteFixedProbeCurvatureScalarBranchJet4,
    CurvatureScalarBranchJet4.vMinus, CurvatureScalarBranchJet4.vPlus,
    CurvatureScalarBranchJet4.alpha, CurvatureScalarBranchJet4.beta]
  split <;>
    simp [
      reconstructedScalarAmplitudeA, reconstructedScalarAmplitudeB,
      smoothScalarAmplitude,
      reconstructedDiagonalAField, reconstructedDiagonalBField,
      oneForm4ContinuousLinearMap_continuousCovectorCoordinates,
      smoothTimelikeCurvatureEigenCovector,
      smoothSpacelikeCurvatureEigenCovector, smoothMetricDualCovector,
      smoothNormalizeTimelike, smoothNormalizeSpacelike,
      normalizeTimelike, normalizeSpacelike, smoothMetricPairing,
      smoothMatrixProjectedVector, curvatureCoordinateDirection_eq_piBasisFun,
      Matrix.toLin'_apply, continuousBilinFormToBilin]

/-- A realized branch patch whose jet is the actual fixed-probe jet has, as
its sum field, exactly the detector's literal `relativeMinus=false`
candidate. -/
theorem RealizedCurvatureScalarBranchPatch4.plusField_eq_actualMetricCandidate
    {U : Set CurvatureCoordinateSpace4}
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (i j : Fin 4)
    (hjet : ∀ z, B.jet z = actualMetricScalarBranchJetField4 g i j z) :
    B.plusField = fun z => oneForm4ContinuousLinearMap
      (actualMetricScalarOneFormCandidateField4 g i j false z) := by
  funext z
  simp only [RealizedCurvatureScalarBranchPatch4.plusField,
    RealizedCurvatureScalarBranchPatch4.alphaField,
    RealizedCurvatureScalarBranchPatch4.betaField, Pi.add_apply]
  rw [hjet z]
  simp [actualMetricScalarOneFormCandidateField4,
    CurvatureScalarBranchJet4.vPlus]

/-- The corresponding equality for the literal
`relativeMinus=true` candidate. -/
theorem RealizedCurvatureScalarBranchPatch4.minusField_eq_actualMetricCandidate
    {U : Set CurvatureCoordinateSpace4}
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (i j : Fin 4)
    (hjet : ∀ z, B.jet z = actualMetricScalarBranchJetField4 g i j z) :
    B.minusField = fun z => oneForm4ContinuousLinearMap
      (actualMetricScalarOneFormCandidateField4 g i j true z) := by
  funext z
  simp only [RealizedCurvatureScalarBranchPatch4.minusField,
    RealizedCurvatureScalarBranchPatch4.alphaField,
    RealizedCurvatureScalarBranchPatch4.betaField, Pi.sub_apply]
  rw [hjet z]
  simp [actualMetricScalarOneFormCandidateField4,
    CurvatureScalarBranchJet4.vMinus]

/-- Fixed-probe form of the actual-metric scalar entrance.  Once one
coordinate probe hits each of the two reconstructed rank-one eigenlines with
the required causal sign, only the relative-sign bit remains to be searched.
This is the form that can be applied pointwise with the *same* probes on a
small regular patch. -/
theorem exists_actualMetricRelativeSignScalarBranch_eq_or_neg_of_physicalCovector
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (v : CurvatureCoordinateSpace4 →ₗ[ℝ] ℝ)
    (vSharp : CurvatureCoordinateSpace4)
    (basis : Basis (Fin 4) ℝ CurvatureCoordinateSpace4)
    (horth : ∀ i j,
      continuousBilinFormToBilin (g z) (basis i) (basis j) =
        if i = j then minkowskiSign i else 0)
    (heigenA : Matrix.toLin' (actualMixedRicciField4 g z) (basis 0) =
      actualRicciComplementaryRootAField4 g z • basis 0)
    (heigenMinus : Matrix.toLin' (actualMixedRicciField4 g z) (basis 1) =
      (-actualRicciProtectedRootField4 g z) • basis 1)
    (heigenB : Matrix.toLin' (actualMixedRicciField4 g z) (basis 2) =
      actualRicciComplementaryRootBField4 g z • basis 2)
    (heigenPlus : Matrix.toLin' (actualMixedRicciField4 g z) (basis 3) =
      actualRicciProtectedRootField4 g z • basis 3)
    (hdual : ∀ y, continuousBilinFormToBilin (g z) y vSharp = v y)
    (hminusNonresonance :
      -(2 * actualRicciProtectedRootField4 g z) ≠
        actualRicciComplementaryRootAField4 g z +
          actualRicciComplementaryRootBField4 g z)
    (hplusNonresonance :
      2 * actualRicciProtectedRootField4 g z ≠
        actualRicciComplementaryRootAField4 g z +
          actualRicciComplementaryRootBField4 g z)
    (hrecon :
      let R := Matrix.toLin' (actualMixedRicciField4 g z)
      let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
      R * V + V * R -
          (actualRicciComplementaryRootAField4 g z +
            actualRicciComplementaryRootBField4 g z) • V =
        R * R - actualRicciReconstructedQSqField4 g z •
          (1 : Module.End ℝ CurvatureCoordinateSpace4))
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (i j : Fin 4)
    (hprobeA :
      let gb := continuousBilinFormToBilin (g z)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g z)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB :
      let gb := continuousBilinFormToBilin (g z)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g z)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j))) :
    ∃ relativeMinus : Bool,
      (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          v ∨
        (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          -v := by
  let G := coordinateMetricMatrixField4 g z
  let Rm := actualMixedRicciField4 g z
  let R := Matrix.toLin' Rm
  let gb := continuousBilinFormToBilin (g z)
  let a := actualRicciComplementaryRootAField4 g z
  let b := actualRicciComplementaryRootBField4 g z
  let q := actualRicciProtectedRootField4 g z
  let qSq := actualRicciReconstructedQSqField4 g z
  let PA := actualRicciComplementaryProjectorAField4 g z
  let PB := actualRicciComplementaryProjectorBField4 g z
  let P := Matrix.toLin' PA
  let Q := Matrix.toLin' PB
  have hranks := halgebraic.scalarProjectorRanks
  have halgebraic' := halgebraic
  unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic'
  dsimp only at halgebraic'
  rcases halgebraic' with
    ⟨hGsym, _, _, hRself, _, _, hqSqPos, _,
      haMinus, hab, haPlus, hminusB, _, hbPlus,
      hPAidem, hPBidem, _, _, _, _, _⟩
  have hself : MetricSelfAdjoint gb R := by
    change MetricSelfAdjoint (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (actualMixedRicciField4 g z))
    rw [← coordinateMetricMatrixField4_toBilin' g z]
    exact matrixMetricSelfAdjoint_of_mul_transpose_eq G Rm hGsym hRself
  have hqSq : q ^ 2 = qSq := by
    exact Real.sq_sqrt (le_of_lt hqSqPos)
  have hP : P.comp P = P := by
    simpa only [P, PA, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hPAidem
  have hQ : Q.comp Q = Q := by
    simpa only [Q, PB, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hPBidem
  have hPA : P (basis 0) = basis 0 := by
    change Matrix.toLin' (actualRicciComplementaryProjectorAField4 g z)
      (basis 0) = basis 0
    rw [actualRicciComplementaryProjectorAField4,
      matrixFourRootProjectorField_toLin']
    exact fourRootProjector_apply_eq_self
      (Matrix.toLin' (actualMixedRicciField4 g z))
      (actualRicciComplementaryRootAField4 g z)
      (-actualRicciProtectedRootField4 g z)
      (actualRicciComplementaryRootBField4 g z)
      (actualRicciProtectedRootField4 g z)
      haMinus hab haPlus (basis 0) heigenA
  have hQB : Q (basis 2) = basis 2 := by
    change Matrix.toLin' (actualRicciComplementaryProjectorBField4 g z)
      (basis 2) = basis 2
    rw [actualRicciComplementaryProjectorBField4,
      matrixFourRootProjectorField_toLin']
    exact fourRootProjector_apply_eq_self
      (Matrix.toLin' (actualMixedRicciField4 g z))
      (actualRicciComplementaryRootBField4 g z)
      (actualRicciComplementaryRootAField4 g z)
      (-actualRicciProtectedRootField4 g z)
      (actualRicciProtectedRootField4 g z)
      hab.symm hminusB.symm hbPlus (basis 2) heigenB
  obtain ⟨relativeMinus, hbranch⟩ :=
    exists_projectedProbeScalarBranch_eq_or_neg_of_reconstructionEquation
      gb R v vSharp basis a b q qSq horth hself
      heigenA heigenMinus heigenB heigenPlus hab hqSq
      hminusNonresonance hplusNonresonance hdual hrecon
      P Q hranks.1 hranks.2 hP hQ hPA hQB
      ((Pi.basisFun ℝ (Fin 4)) i) ((Pi.basisFun ℝ (Fin 4)) j)
      hprobeA hprobeB
  refine ⟨relativeMinus, ?_⟩
  rw [actualMetricScalarOneFormCandidate_toLinearMap]
  exact hbranch

/-- **Actual-metric finite-probe scalar entrance.** Suppose the actual mixed
Ricci endomorphism has a pseudo-orthonormal eigenbasis with the four generic
roots reconstructed by the metric detector, and a physical rank-one scalar
covector satisfies the Ricci reconstruction equation.  The algebraic entrance
and intrinsic causal labeling then force the finite coordinate-probe list to
contain that physical covector, up to its unavoidable global sign.

In particular, the polynomial projectors, their rank-one property, both probe
indices, both reconstructed amplitudes, and the relative-sign bit are outputs;
none is supplied as physical data. -/
theorem exists_actualMetricFiniteProbeScalarBranch_eq_or_neg_of_physicalCovector
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (v : CurvatureCoordinateSpace4 →ₗ[ℝ] ℝ)
    (vSharp : CurvatureCoordinateSpace4)
    (basis : Basis (Fin 4) ℝ CurvatureCoordinateSpace4)
    (horth : ∀ i j,
      continuousBilinFormToBilin (g z) (basis i) (basis j) =
        if i = j then minkowskiSign i else 0)
    (heigenA : Matrix.toLin' (actualMixedRicciField4 g z) (basis 0) =
      actualRicciComplementaryRootAField4 g z • basis 0)
    (heigenMinus : Matrix.toLin' (actualMixedRicciField4 g z) (basis 1) =
      (-actualRicciProtectedRootField4 g z) • basis 1)
    (heigenB : Matrix.toLin' (actualMixedRicciField4 g z) (basis 2) =
      actualRicciComplementaryRootBField4 g z • basis 2)
    (heigenPlus : Matrix.toLin' (actualMixedRicciField4 g z) (basis 3) =
      actualRicciProtectedRootField4 g z • basis 3)
    (hdual : ∀ y, continuousBilinFormToBilin (g z) y vSharp = v y)
    (hminusNonresonance :
      -(2 * actualRicciProtectedRootField4 g z) ≠
        actualRicciComplementaryRootAField4 g z +
          actualRicciComplementaryRootBField4 g z)
    (hplusNonresonance :
      2 * actualRicciProtectedRootField4 g z ≠
        actualRicciComplementaryRootAField4 g z +
          actualRicciComplementaryRootBField4 g z)
    (hrecon :
      let R := Matrix.toLin' (actualMixedRicciField4 g z)
      let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
      R * V + V * R -
          (actualRicciComplementaryRootAField4 g z +
            actualRicciComplementaryRootBField4 g z) • V =
        R * R - actualRicciReconstructedQSqField4 g z •
          (1 : Module.End ℝ CurvatureCoordinateSpace4))
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (hcausal : IsActualMetricScalarEigenlineCausalAt4 g z) :
    ∃ i j : Fin 4, ∃ relativeMinus : Bool,
      (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          v ∨
        (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          -v := by
  let G := coordinateMetricMatrixField4 g z
  let Rm := actualMixedRicciField4 g z
  let R := Matrix.toLin' Rm
  let gb := continuousBilinFormToBilin (g z)
  let a := actualRicciComplementaryRootAField4 g z
  let b := actualRicciComplementaryRootBField4 g z
  let q := actualRicciProtectedRootField4 g z
  let qSq := actualRicciReconstructedQSqField4 g z
  let PA := actualRicciComplementaryProjectorAField4 g z
  let PB := actualRicciComplementaryProjectorBField4 g z
  let P := Matrix.toLin' PA
  let Q := Matrix.toLin' PB
  have hranks := halgebraic.scalarProjectorRanks
  have halgebraic' := halgebraic
  unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic'
  dsimp only at halgebraic'
  rcases halgebraic' with
    ⟨hGsym, _, _, hRself, _, _, hqSqPos, _,
      haMinus, hab, haPlus, hminusB, _, hbPlus,
      hPAidem, hPBidem, _, _, _, _, _⟩
  have hself : MetricSelfAdjoint gb R := by
    change MetricSelfAdjoint (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (actualMixedRicciField4 g z))
    rw [← coordinateMetricMatrixField4_toBilin' g z]
    exact matrixMetricSelfAdjoint_of_mul_transpose_eq G Rm hGsym hRself
  have hqSq : q ^ 2 = qSq := by
    exact Real.sq_sqrt (le_of_lt hqSqPos)
  have hP : P.comp P = P := by
    simpa only [P, PA, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hPAidem
  have hQ : Q.comp Q = Q := by
    simpa only [Q, PB, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hPBidem
  have hPA : P (basis 0) = basis 0 := by
    change Matrix.toLin' (actualRicciComplementaryProjectorAField4 g z)
      (basis 0) = basis 0
    rw [actualRicciComplementaryProjectorAField4,
      matrixFourRootProjectorField_toLin']
    exact fourRootProjector_apply_eq_self
      (Matrix.toLin' (actualMixedRicciField4 g z))
      (actualRicciComplementaryRootAField4 g z)
      (-actualRicciProtectedRootField4 g z)
      (actualRicciComplementaryRootBField4 g z)
      (actualRicciProtectedRootField4 g z)
      haMinus hab haPlus (basis 0) heigenA
  have hQB : Q (basis 2) = basis 2 := by
    change Matrix.toLin' (actualRicciComplementaryProjectorBField4 g z)
      (basis 2) = basis 2
    rw [actualRicciComplementaryProjectorBField4,
      matrixFourRootProjectorField_toLin']
    exact fourRootProjector_apply_eq_self
      (Matrix.toLin' (actualMixedRicciField4 g z))
      (actualRicciComplementaryRootBField4 g z)
      (actualRicciComplementaryRootAField4 g z)
      (-actualRicciProtectedRootField4 g z)
      (actualRicciProtectedRootField4 g z)
      hab.symm hminusB.symm hbPlus (basis 2) heigenB
  unfold IsActualMetricScalarEigenlineCausalAt4 at hcausal
  dsimp only at hcausal
  obtain ⟨i, hi⟩ :=
    exists_projectedBasisTimelikeVector_of_rankOneRange gb
      (Pi.basisFun ℝ (Fin 4)) P hranks.1 hcausal.1
  obtain ⟨j, hj⟩ :=
    exists_projectedBasisSpacelikeVector_of_rankOneRange gb
      (Pi.basisFun ℝ (Fin 4)) Q hranks.2 hcausal.2
  obtain ⟨relativeMinus, hbranch⟩ :=
    exists_projectedProbeScalarBranch_eq_or_neg_of_reconstructionEquation
      gb R v vSharp basis a b q qSq horth hself
      heigenA heigenMinus heigenB heigenPlus hab hqSq
      hminusNonresonance hplusNonresonance hdual hrecon
      P Q hranks.1 hranks.2 hP hQ hPA hQB
      ((Pi.basisFun ℝ (Fin 4)) i) ((Pi.basisFun ℝ (Fin 4)) j) hi hj
  refine ⟨i, j, relativeMinus, ?_⟩
  rw [actualMetricScalarOneFormCandidate_toLinearMap]
  exact hbranch

/-- The frozen, choice-independent physical entrance for scalar
identifiability.  It contains only the Ricci data supplied by a genuine EMD
solution and the generic simple-spectrum frame on which the theorem is
claimed.  In particular, it contains no detector probe, relative-sign bit,
orientation bit, Maxwell-frame choice, or fourth-order component choice. -/
structure ChoiceIndependentActualMetricEMDRicciWitnessAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) where
  scalarCovector : CurvatureCoordinateSpace4 →ₗ[ℝ] ℝ
  scalarVector : CurvatureCoordinateSpace4
  maxwellRicci : Module.End ℝ CurvatureCoordinateSpace4
  ricciEigenbasis : Basis (Fin 4) ℝ CurvatureCoordinateSpace4
  orthonormal : ∀ i j,
    continuousBilinFormToBilin (g z)
        (ricciEigenbasis i) (ricciEigenbasis j) =
      if i = j then minkowskiSign i else 0
  eigenA : Matrix.toLin' (actualMixedRicciField4 g z)
      (ricciEigenbasis 0) =
    actualRicciComplementaryRootAField4 g z • ricciEigenbasis 0
  eigenMinus : Matrix.toLin' (actualMixedRicciField4 g z)
      (ricciEigenbasis 1) =
    (-actualRicciProtectedRootField4 g z) • ricciEigenbasis 1
  eigenB : Matrix.toLin' (actualMixedRicciField4 g z)
      (ricciEigenbasis 2) =
    actualRicciComplementaryRootBField4 g z • ricciEigenbasis 2
  eigenPlus : Matrix.toLin' (actualMixedRicciField4 g z)
      (ricciEigenbasis 3) =
    actualRicciProtectedRootField4 g z • ricciEigenbasis 3
  metricDual : ∀ y,
    continuousBilinFormToBilin (g z) y scalarVector = scalarCovector y
  minusNonresonance :
    -(2 * actualRicciProtectedRootField4 g z) ≠
      actualRicciComplementaryRootAField4 g z +
        actualRicciComplementaryRootBField4 g z
  plusNonresonance :
    2 * actualRicciProtectedRootField4 g z ≠
      actualRicciComplementaryRootAField4 g z +
        actualRicciComplementaryRootBField4 g z
  ricciDecomposition :
    Matrix.toLin' (actualMixedRicciField4 g z) =
      maxwellRicci + rankOneEndomorphism scalarCovector
        ((2 : ℝ)⁻¹ • scalarVector)
  maxwellSquare :
    maxwellRicci * maxwellRicci =
      actualRicciReconstructedQSqField4 g z •
        (1 : Module.End ℝ CurvatureCoordinateSpace4)
  maxwellTrace : LinearMap.trace ℝ CurvatureCoordinateSpace4 maxwellRicci = 0
  maxwellPositiveEnergy : HasPositiveMaxwellEnergyDensity
    (continuousBilinFormToBilin (g z)) maxwellRicci
  scalarTrace :
    scalarCovector ((2 : ℝ)⁻¹ • scalarVector) =
      actualRicciComplementaryRootAField4 g z +
        actualRicciComplementaryRootBField4 g z

/-- Fixed-probe geometric scalar identifiability from the
choice-independent EMD Ricci witness.  This is the pointwise theorem needed
on a regular neighborhood after the probe indices have been selected once at
the base point. -/
theorem exists_actualMetricRelativeSignScalarBranch_eq_or_neg_of_emdRicciWitness
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (i j : Fin 4)
    (hprobeA :
      let gb := continuousBilinFormToBilin (g z)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g z)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB :
      let gb := continuousBilinFormToBilin (g z)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g z)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j))) :
    ∃ relativeMinus : Bool,
      (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          W.scalarCovector ∨
        (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          -W.scalarCovector := by
  have hrecon := reconstructionEquation_of_rankOneRicciDecomposition
    (Matrix.toLin' (actualMixedRicciField4 g z)) W.maxwellRicci
    W.scalarCovector W.scalarVector
    (actualRicciComplementaryRootAField4 g z +
      actualRicciComplementaryRootBField4 g z)
    (actualRicciReconstructedQSqField4 g z)
    W.ricciDecomposition W.maxwellSquare W.scalarTrace
  exact
    exists_actualMetricRelativeSignScalarBranch_eq_or_neg_of_physicalCovector
      g z W.scalarCovector W.scalarVector W.ricciEigenbasis W.orthonormal
      W.eigenA W.eigenMinus W.eigenB W.eigenPlus W.metricDual
      W.minusNonresonance W.plusNonresonance hrecon halgebraic i j
      hprobeA hprobeB

/-- Choice-independent EMD Ricci data varying over a patch.  The physical
scalar field is continuous and closed, while each point supplies the
geometric Ricci witness used by the pointwise identifiability theorem. -/
structure ChoiceIndependentActualMetricEMDRicciWitnessPatch4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (U : Set CurvatureCoordinateSpace4) where
  scalarOneForm : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  scalarContinuous : ContinuousOn scalarOneForm U
  scalarClosed : IsClosedScalarOneFormOn scalarOneForm U
  scalarNonzero : ∀ z ∈ U, scalarOneForm z ≠ 0
  witnessAt : ∀ z ∈ U, ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z
  scalarCovector_eq : ∀ z (hz : z ∈ U),
    (witnessAt z hz).scalarCovector = (scalarOneForm z).toLinearMap

@[simp] theorem scalarRaisedVector_neg_oneFormField
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    scalarRaisedVector gInv (fun y => -v y) z =
      -scalarRaisedVector gInv v z := by
  ext i
  simp [scalarRaisedVector, Matrix.mulVec, dotProduct]

/-- The mixed rank-one scalar tensor is insensitive to the unavoidable
overall sign of the recovered scalar covector. -/
theorem scalarContributionMatrixField_neg_oneFormField
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    scalarContributionMatrixField gInv (fun y => -v y) z =
      scalarContributionMatrixField gInv v z := by
  ext i j
  simp [scalarContributionMatrixField]

@[simp] theorem scalarContributionTraceField_neg_oneFormField
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    scalarContributionTraceField gInv (fun y => -v y) z =
      scalarContributionTraceField gInv v z := by
  simp [scalarContributionTraceField, oneForm4Evaluate]

theorem scalarContributionMatrixField_congr_at
    {X : Type*} (gInv : X → Matrix4) (v w : X → OneForm4) (z : X)
    (h : v z = w z) :
    scalarContributionMatrixField gInv v z =
      scalarContributionMatrixField gInv w z := by
  ext i j
  simp [scalarContributionMatrixField, scalarRaisedVector, h]

theorem scalarContributionTraceField_congr_at
    {X : Type*} (gInv : X → Matrix4) (v w : X → OneForm4) (z : X)
    (h : v z = w z) :
    scalarContributionTraceField gInv v z =
      scalarContributionTraceField gInv w z := by
  simp [scalarContributionTraceField, scalarRaisedVector, h]

/-- Matrix inversion raises the coordinate components of the physical EMD
scalar covector back to the metric-dual vector in the choice-independent
Ricci witness. -/
theorem scalarRaisedVector_continuousCovectorCoordinates_eq_emdScalarVector
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z)
    (v : CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : W.scalarCovector = v.toLinearMap)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z) :
    scalarRaisedVector
        (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
        (fun _ => continuousCovectorCoordinates v) z =
      W.scalarVector := by
  let G := coordinateMetricMatrixField4 g z
  have hdet : Matrix.det G ≠ 0 := by
    have hdetNeg : Matrix.det G < 0 := by
      unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic
      exact halgebraic.2.1
    exact ne_of_lt hdetNeg
  have hunit : IsUnit (Matrix.det G) := isUnit_iff_ne_zero.mpr hdet
  have hinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit
  have hGv : G.mulVec W.scalarVector = continuousCovectorCoordinates v := by
    funext i
    have hdual := W.metricDual (curvatureCoordinateDirection i)
    rw [hv] at hdual
    have hmetric := coordinateMetricMatrixField4_toBilin' g z
    rw [← hmetric] at hdual
    calc
      (G.mulVec W.scalarVector) i =
          Matrix.toBilin' G (curvatureCoordinateDirection i)
            W.scalarVector := by
              simp [Matrix.toBilin'_apply', curvatureCoordinateDirection,
                dotProduct]
      _ = v (curvatureCoordinateDirection i) := hdual
      _ = continuousCovectorCoordinates v i := rfl
  unfold scalarRaisedVector
  dsimp only
  change (G⁻¹).mulVec (continuousCovectorCoordinates v) = W.scalarVector
  rw [← hGv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem oneForm4_eq_continuousCovectorCoordinates_of_toContinuousLinearMap_eq
    (u : OneForm4) (v : CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (h : oneForm4ContinuousLinearMap u = v) :
    u = continuousCovectorCoordinates v := by
  ext i
  have hi := congrArg
    (fun f : CurvatureCoordinateSpace4 →L[ℝ] ℝ =>
      f (curvatureCoordinateDirection i)) h
  simpa [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    continuousCovectorCoordinates, curvatureCoordinateDirection] using hi

/-- A recovered scalar candidate in the physical `±` orbit constructs
exactly the physical rank-one Ricci contribution and trace.  Thus the sign
ambiguity has disappeared before the Maxwell residual is formed. -/
theorem scalarContribution_eq_emdRicciContribution_of_candidate_orbit
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z)
    (v : CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : W.scalarCovector = v.toLinearMap)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (u : OneForm4)
    (horbit : oneForm4ContinuousLinearMap u = v ∨
      oneForm4ContinuousLinearMap u = -v) :
    Matrix.toLin'
        (scalarContributionMatrixField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (fun _ => u) z) =
        rankOneEndomorphism W.scalarCovector
          ((2 : ℝ)⁻¹ • W.scalarVector) ∧
      scalarContributionTraceField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (fun _ => u) z =
        W.scalarCovector ((2 : ℝ)⁻¹ • W.scalarVector) := by
  have hraised :=
    scalarRaisedVector_continuousCovectorCoordinates_eq_emdScalarVector
      g z W v hv halgebraic
  rcases horbit with hplus | hminus
  · have hu :=
      oneForm4_eq_continuousCovectorCoordinates_of_toContinuousLinearMap_eq
        u v hplus
    subst u
    constructor
    · rw [scalarContributionMatrixField_toLin', hraised,
        oneForm4ContinuousLinearMap_continuousCovectorCoordinates, ← hv]
    · unfold scalarContributionTraceField
      rw [hraised]
      change oneForm4ContinuousLinearMap
          (continuousCovectorCoordinates v)
          ((2 : ℝ)⁻¹ • W.scalarVector) =
        W.scalarCovector ((2 : ℝ)⁻¹ • W.scalarVector)
      rw [oneForm4ContinuousLinearMap_continuousCovectorCoordinates]
      exact (LinearMap.congr_fun hv
        ((2 : ℝ)⁻¹ • W.scalarVector)).symm

  · have hu : u = -continuousCovectorCoordinates v := by
      have hneg : oneForm4ContinuousLinearMap (-u) = v := by
        ext x
        have hx := congrArg
          (fun f : CurvatureCoordinateSpace4 →L[ℝ] ℝ => f x) hminus
        simpa [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate] using
          congrArg Neg.neg hx
      have hcoords :=
        oneForm4_eq_continuousCovectorCoordinates_of_toContinuousLinearMap_eq
          (-u) v hneg
      simpa using congrArg Neg.neg hcoords
    subst u
    rw [show (fun _ : CurvatureCoordinateSpace4 =>
        -continuousCovectorCoordinates v) =
        fun y => -(fun _ : CurvatureCoordinateSpace4 =>
          continuousCovectorCoordinates v) y by rfl]
    rw [scalarContributionMatrixField_neg_oneFormField,
      scalarContributionTraceField_neg_oneFormField]
    constructor
    · rw [scalarContributionMatrixField_toLin', hraised,
        oneForm4ContinuousLinearMap_continuousCovectorCoordinates, ← hv]
    · unfold scalarContributionTraceField
      rw [hraised]
      change oneForm4ContinuousLinearMap
          (continuousCovectorCoordinates v)
          ((2 : ℝ)⁻¹ • W.scalarVector) =
        W.scalarCovector ((2 : ℝ)⁻¹ • W.scalarVector)
      rw [oneForm4ContinuousLinearMap_continuousCovectorCoordinates]
      exact (LinearMap.congr_fun hv
        ((2 : ℝ)⁻¹ • W.scalarVector)).symm

/-- The choice-independent physical Ricci decomposition discharges the
detector's literal matrix reconstruction obstruction for any recovered
scalar candidate in the physical `±` orbit. -/
theorem actualMetricReconstructionObstruction4_eq_zero_of_emdRicciWitness
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z)
    (v : CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : W.scalarCovector = v.toLinearMap)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (horbit : oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) = v ∨
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) = -v) :
    actualMetricReconstructionObstruction4 g choice z = 0 := by
  let u := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus z
  have hVT := scalarContribution_eq_emdRicciContribution_of_candidate_orbit
    g z W v hv halgebraic u (by simpa [u] using horbit)
  have hV : Matrix.toLin'
      (actualMetricScalarContributionCandidateField4 g choice z) =
      rankOneEndomorphism W.scalarCovector
        ((2 : ℝ)⁻¹ • W.scalarVector) := by
    unfold actualMetricScalarContributionCandidateField4
    calc
      Matrix.toLin' (scalarContributionMatrixField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus) z) =
        Matrix.toLin' (scalarContributionMatrixField
        (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
        (fun _ => u) z) := congrArg Matrix.toLin'
          (scalarContributionMatrixField_congr_at
            (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus) (fun _ => u) z rfl)
      _ = _ := hVT.1
  have htrace : scalarContributionTraceField
      (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus) z =
      actualRicciComplementaryRootAField4 g z +
        actualRicciComplementaryRootBField4 g z := by
    calc
      scalarContributionTraceField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus) z =
        scalarContributionTraceField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (fun _ => u) z :=
            scalarContributionTraceField_congr_at
              (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
              (actualMetricScalarOneFormCandidateField4 g
                choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                choice.relativeMinus) (fun _ => u) z rfl
      _ = _ := hVT.2.trans W.scalarTrace
  have hrecon := reconstructionEquation_of_rankOneRicciDecomposition
    (Matrix.toLin' (actualMixedRicciField4 g z)) W.maxwellRicci
    W.scalarCovector W.scalarVector
    (actualRicciComplementaryRootAField4 g z +
      actualRicciComplementaryRootBField4 g z)
    (actualRicciReconstructedQSqField4 g z)
    W.ricciDecomposition W.maxwellSquare W.scalarTrace
  unfold actualMetricReconstructionObstruction4
  dsimp only
  rw [sub_eq_zero]
  apply Matrix.toLin'.injective
  simp only [map_add, map_sub, map_smul, Matrix.toLin'_mul,
    Matrix.toLin'_one, hV, htrace]
  simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id] using hrecon

/-- Converse coordinate form of metric self-adjointness. -/
theorem mul_transpose_eq_of_matrixMetricSelfAdjoint
    (G S : Matrix4) (hG : G.transpose = G)
    (hself : MetricSelfAdjoint (Matrix.toBilin' G) (Matrix.toLin' S)) :
    (G * S).transpose = G * S := by
  have hforms :
      (Matrix.toBilin' G).compLeft (Matrix.toLin' S) =
        (Matrix.toBilin' G).compRight (Matrix.toLin' S) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact hself x y
  have hmat := congrArg LinearMap.BilinForm.toMatrix' hforms
  simp only [LinearMap.BilinForm.toMatrix'_compLeft,
    LinearMap.BilinForm.toMatrix'_compRight,
    LinearMap.BilinForm.toMatrix'_toBilin',
    LinearMap.toMatrix'_toLin'] at hmat
  calc
    (G * S).transpose = S.transpose * G.transpose := Matrix.transpose_mul G S
    _ = S.transpose * G := by rw [hG]
    _ = G * S := hmat

/-- Once the scalar candidate lies in the physical sign orbit, the detector's
matrix residual is exactly the choice-independent physical Maxwell Ricci
endomorphism. -/
theorem actualMetricMaxwellResidual_toLin_eq_emdRicciWitness
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z)
    (v : CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : W.scalarCovector = v.toLinearMap)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (horbit : oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) = v ∨
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) = -v) :
    Matrix.toLin' (actualMetricMaxwellResidualCandidateField4 g choice z) =
      W.maxwellRicci := by
  have hVT := scalarContribution_eq_emdRicciContribution_of_candidate_orbit
    g z W v hv halgebraic
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z) horbit
  have hV : Matrix.toLin'
      (actualMetricScalarContributionCandidateField4 g choice z) =
      rankOneEndomorphism W.scalarCovector
        ((2 : ℝ)⁻¹ • W.scalarVector) := by
    unfold actualMetricScalarContributionCandidateField4
    calc
      Matrix.toLin' (scalarContributionMatrixField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus) z) =
        Matrix.toLin' (scalarContributionMatrixField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (fun _ => actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) z) := congrArg Matrix.toLin'
              (scalarContributionMatrixField_congr_at
                (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
                (actualMetricScalarOneFormCandidateField4 g
                  choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                  choice.relativeMinus)
                (fun _ => actualMetricScalarOneFormCandidateField4 g
                  choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                  choice.relativeMinus z) z rfl)
      _ = _ := hVT.1
  unfold actualMetricMaxwellResidualCandidateField4
    curvatureMaxwellResidualField maxwellResidual
  rw [map_sub, hV]
  have hdecomp := W.ricciDecomposition
  rw [hdecomp]
  module

/-- A physical EMD Ricci witness and recovered scalar orbit discharge the
entire packaged Maxwell algebra gate: square law, self-adjointness, and both
principal-projector identities. -/
theorem isActualMetricMaxwellEntranceAt4_of_emdRicciWitness
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z)
    (v : CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (hv : W.scalarCovector = v.toLinearMap)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (horbit : oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) = v ∨
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) = -v) :
    IsActualMetricMaxwellEntranceAt4 g choice z := by
  let G := coordinateMetricMatrixField4 g z
  let Rm := actualMixedRicciField4 g z
  let R := Matrix.toLin' Rm
  let Vm := actualMetricScalarContributionCandidateField4 g choice z
  let V := rankOneEndomorphism W.scalarCovector
    ((2 : ℝ)⁻¹ • W.scalarVector)
  let Sm := actualMetricMaxwellResidualCandidateField4 g choice z
  let S := Matrix.toLin' Sm
  let qSq := actualRicciReconstructedQSqField4 g z
  let P := actualMetricMaxwellMinusProjectorCandidateField4 g choice z
  let Q := actualMetricMaxwellPlusProjectorCandidateField4 g choice z
  have halgebraic' := halgebraic
  unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic'
  dsimp only at halgebraic'
  rcases halgebraic' with
    ⟨hGsym, _, _, hRselfMatrix, _, _, hqSqPos, _⟩
  have hVT := scalarContribution_eq_emdRicciContribution_of_candidate_orbit
    g z W v hv halgebraic
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z) horbit
  have hV : Matrix.toLin' Vm = V := by
    unfold Vm V actualMetricScalarContributionCandidateField4
    calc
      Matrix.toLin' (scalarContributionMatrixField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus) z) =
        Matrix.toLin' (scalarContributionMatrixField
          (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
          (fun _ => actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) z) := congrArg Matrix.toLin'
              (scalarContributionMatrixField_congr_at
                (fun y => (coordinateMetricMatrixField4 g y)⁻¹)
                (actualMetricScalarOneFormCandidateField4 g
                  choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                  choice.relativeMinus)
                (fun _ => actualMetricScalarOneFormCandidateField4 g
                  choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                  choice.relativeMinus z) z rfl)
      _ = _ := hVT.1
  have hS : S = W.maxwellRicci := by
    change Matrix.toLin' Sm = W.maxwellRicci
    rw [show Sm = Rm - Vm by
      rfl, map_sub, hV]
    change R - V = W.maxwellRicci
    have hdecomp := W.ricciDecomposition
    change R = W.maxwellRicci + V at hdecomp
    rw [hdecomp]
    module
  have hSq : Sm * Sm = qSq • (1 : Matrix4) := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, map_smul, Matrix.toLin'_one]
    rw [show Matrix.toLin' Sm = S by rfl, hS]
    simpa [qSq, Module.End.mul_eq_comp, Module.End.one_eq_id] using
      W.maxwellSquare
  have hgbSymm : (continuousBilinFormToBilin (g z)).IsSymm := by
    rw [← coordinateMetricMatrixField4_toBilin' g z]
    exact Matrix.isSymm_toBilin'_iff_isSymm.mpr hGsym
  have hRself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z)) R := by
    rw [← coordinateMetricMatrixField4_toBilin' g z]
    exact matrixMetricSelfAdjoint_of_mul_transpose_eq
      G Rm hGsym hRselfMatrix
  have hVself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z)) V := by
    apply rankOneEndomorphism_metricSelfAdjoint_of_dual
      (continuousBilinFormToBilin (g z)) hgbSymm W.scalarCovector
      ((2 : ℝ)⁻¹ • W.scalarVector) (2 : ℝ)⁻¹
    intro y
    simp only [LinearMap.BilinForm.smul_left]
    rw [hgbSymm.eq W.scalarVector y, W.metricDual]
  have hSself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z)) S := by
    rw [hS]
    have hM : W.maxwellRicci = R - V := by
      have hdecomp := W.ricciDecomposition
      change R = W.maxwellRicci + V at hdecomp
      rw [hdecomp]
      module
    rw [hM]
    exact hRself.sub hVself
  have hSselfMatrix : (G * Sm).transpose = G * Sm := by
    apply mul_transpose_eq_of_matrixMetricSelfAdjoint G Sm hGsym
    rwa [coordinateMetricMatrixField4_toBilin' g z]
  have hprojectors := curvatureMaxwellPrincipalProjectorFields_structural
    (actualMetricMaxwellResidualCandidateField4 g choice)
    (actualRicciReconstructedQSqField4 g) z hqSqPos hSq
  unfold IsActualMetricMaxwellEntranceAt4
  dsimp only
  exact ⟨hSq, hSselfMatrix, hprojectors⟩

/-- On a patch carrying the choice-independent EMD Ricci witness, any one
fixed pair of admissible coordinate probes makes the two literal
relative-sign candidates cover the physical scalar `±`-orbit pointwise.
There is no point-dependent probe choice in this conclusion. -/
theorem actualMetricFixedProbeScalarBranches_cover_physicalOrbit
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ z ∈ U, IsActualMetricAlgebraicEntranceAt4 g z)
    (i j : Fin 4)
    (hprobeA : ∀ z ∈ U,
      let gb := continuousBilinFormToBilin (g z)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g z)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ z ∈ U,
      let gb := continuousBilinFormToBilin (g z)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g z)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j))) :
    ∀ z ∈ U,
      ((oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j false z) =
            W.scalarOneForm z) ∨
        (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j false z) =
            -W.scalarOneForm z)) ∨
      ((oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j true z) =
            W.scalarOneForm z) ∨
        (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j true z) =
            -W.scalarOneForm z)) := by
  intro z hz
  obtain ⟨relativeMinus, hbranch⟩ :=
    exists_actualMetricRelativeSignScalarBranch_eq_or_neg_of_emdRicciWitness
      g z (W.witnessAt z hz) (halgebraic z hz) i j
      (hprobeA z hz) (hprobeB z hz)
  have hbranch' :
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z) =
            W.scalarOneForm z ∨
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z) =
            -W.scalarOneForm z := by
    rcases hbranch with hbranch | hbranch
    · apply Or.inl
      ext x
      exact LinearMap.congr_fun
        (hbranch.trans (W.scalarCovector_eq z hz)) x
    · apply Or.inr
      ext x
      have hx := LinearMap.congr_fun
        (hbranch.trans (congrArg Neg.neg (W.scalarCovector_eq z hz))) x
      simpa using hx
  cases relativeMinus
  · exact Or.inl hbranch'
  · exact Or.inr hbranch'

/-- **Choice-independent local scalar-jet entrance for the actual metric.**
On a regular realized fixed-probe patch carrying genuine EMD Ricci data, the
finite detector has a relative-sign choice whose literal fourth-order scalar
closure obstruction vanishes.  Probe indices are fixed on the patch; neither
the physical scalar nor any sign choice is an input to the conclusion. -/
theorem exists_actualMetricScalarClosureObstruction_eq_zero_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0) :
    actualMetricScalarClosureObstruction4 g i j false z = 0 ∨
      actualMetricScalarClosureObstruction4 g i j true z = 0 := by
  have hraw := actualMetricFixedProbeScalarBranches_cover_physicalOrbit
    g W halgebraic i j hprobeA hprobeB
  have hplus := B.plusField_eq_actualMetricCandidate g i j hjet
  have hminus := B.minusField_eq_actualMetricCandidate g i j hjet
  have hcover : ∀ᶠ y in 𝓝 z,
      (B.plusField y = W.scalarOneForm y ∨
          B.plusField y = -W.scalarOneForm y) ∨
        (B.minusField y = W.scalarOneForm y ∨
          B.minusField y = -W.scalarOneForm y) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    have hyCover := hraw y hy
    simpa only [hplus, hminus] using hyCover
  have hobstruction :=
    B.exists_branchObstruction_eq_zero_of_local_orbit
      hopen hz W.scalarOneForm
      ((W.scalarContinuous z hz).continuousAt (hopen.mem_nhds hz))
      (W.scalarNonzero z hz) W.scalarClosed halpha hbeta hcover
  simpa [actualMetricScalarClosureObstruction4, hjet z] using hobstruction

/-- Boolean-selector form of the local scalar-jet entrance. -/
theorem exists_actualMetricScalarClosureChoice_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0) :
    ∃ relativeMinus : Bool,
      actualMetricScalarClosureObstruction4 g i j relativeMinus z = 0 := by
  rcases exists_actualMetricScalarClosureObstruction_eq_zero_of_emdRicciWitnessPatch
      g B hopen hz i j hjet W halgebraic hprobeA hprobeB halpha hbeta with
    hplus | hminus
  · exact ⟨false, hplus⟩
  · exact ⟨true, hminus⟩

/-- The selected Boolean branch carries both facts needed by downstream
composition: physical `±`-orbit membership and its literal closure gate. -/
theorem exists_actualMetricScalarOrbitAndClosureChoice_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0) :
    ∃ relativeMinus : Bool,
      (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z) =
            W.scalarOneForm z ∨
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z) =
            -W.scalarOneForm z) ∧
      actualMetricScalarClosureObstruction4 g i j relativeMinus z = 0 := by
  have hraw := actualMetricFixedProbeScalarBranches_cover_physicalOrbit
    g W halgebraic i j hprobeA hprobeB
  have hplus := B.plusField_eq_actualMetricCandidate g i j hjet
  have hminus := B.minusField_eq_actualMetricCandidate g i j hjet
  have hcover : ∀ᶠ y in 𝓝 z,
      (B.plusField y = W.scalarOneForm y ∨
          B.plusField y = -W.scalarOneForm y) ∨
        (B.minusField y = W.scalarOneForm y ∨
          B.minusField y = -W.scalarOneForm y) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    simpa only [hplus, hminus] using hraw y hy
  have hselected :=
    B.exists_branchOrbit_and_obstruction_eq_zero_of_local_orbit
      hopen hz W.scalarOneForm
      ((W.scalarContinuous z hz).continuousAt (hopen.mem_nhds hz))
      (W.scalarNonzero z hz) W.scalarClosed halpha hbeta hcover
  rcases hselected with hselected | hselected
  · refine ⟨false, ?_, ?_⟩
    · simpa only [hplus] using hselected.1
    · simpa [actualMetricScalarClosureObstruction4, hjet z] using hselected.2
  · refine ⟨true, ?_, ?_⟩
    · simpa only [hminus] using hselected.1
    · simpa [actualMetricScalarClosureObstruction4, hjet z] using hselected.2

/-- Germ-level version of the finite scalar selector. One literal Boolean
branch equals one fixed sign of the physical scalar field throughout a
neighborhood and clears its closure obstruction. -/
theorem exists_actualMetricScalarGermAndClosureChoice_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0) :
    ∃ relativeMinus : Bool,
      (((fun y => oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus y))
            =ᶠ[nhds z] W.scalarOneForm) ∨
        ((fun y => oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus y))
            =ᶠ[nhds z] fun y => -W.scalarOneForm y)) ∧
      actualMetricScalarClosureObstruction4 g i j relativeMinus z = 0 := by
  have hraw := actualMetricFixedProbeScalarBranches_cover_physicalOrbit
    g W halgebraic i j hprobeA hprobeB
  have hplus := B.plusField_eq_actualMetricCandidate g i j hjet
  have hminus := B.minusField_eq_actualMetricCandidate g i j hjet
  have hcover : ∀ᶠ y in 𝓝 z,
      (B.plusField y = W.scalarOneForm y ∨
          B.plusField y = -W.scalarOneForm y) ∨
        (B.minusField y = W.scalarOneForm y ∨
          B.minusField y = -W.scalarOneForm y) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    simpa only [hplus, hminus] using hraw y hy
  have hselected :=
    B.exists_branchGerm_and_obstruction_eq_zero_of_local_orbit
      hopen hz W.scalarOneForm
      ((W.scalarContinuous z hz).continuousAt (hopen.mem_nhds hz))
      (W.scalarNonzero z hz) W.scalarClosed halpha hbeta hcover
  rcases hselected with hselected | hselected
  · refine ⟨false, ?_, ?_⟩
    · simpa only [hplus] using hselected.1
    · simpa [actualMetricScalarClosureObstruction4, hjet z] using hselected.2
  · refine ⟨true, ?_, ?_⟩
    · simpa only [hminus] using hselected.1
    · simpa [actualMetricScalarClosureObstruction4, hjet z] using hselected.2

/-- A retained fixed scalar branch germ clears the literal closure obstruction
at every sufficiently nearby point, not only at the point where the branch
was selected.  The neighborhood is shrunk so that the original germ is also
a germ at each new base point; closedness of the physical scalar (or its
negative) then identifies the displayed exterior derivative there. -/
theorem eventually_actualMetricScalarClosureObstruction4_eq_zero_of_germ
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (relativeMinus : Bool)
    (hgerm :
      ((fun y => oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g i j relativeMinus y))
          =ᶠ[nhds z] W.scalarOneForm) ∨
      ((fun y => oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g i j relativeMinus y))
          =ᶠ[nhds z] fun y => -W.scalarOneForm y)) :
    ∀ᶠ y in nhds z,
      actualMetricScalarClosureObstruction4 g i j relativeMinus y = 0 := by
  have hclosedNeg :
      IsClosedScalarOneFormOn (fun y => -W.scalarOneForm y) U := by
    constructor
    · exact W.scalarClosed.1.neg
    · intro y hy u w
      change fderiv ℝ (-W.scalarOneForm) y u w =
        fderiv ℝ (-W.scalarOneForm) y w u
      rw [fderiv_neg]
      simp only [neg_apply]
      rw [W.scalarClosed.2 y hy u w]
  have hplus := B.plusField_eq_actualMetricCandidate g i j hjet
  have hminus := B.minusField_eq_actualMetricCandidate g i j hjet
  have hU : ∀ᶠ y in nhds z, y ∈ U := hopen.mem_nhds hz
  cases relativeMinus with
  | false =>
      rcases hgerm with hgerm | hgerm
      · have hbranch : B.plusField =ᶠ[nhds z] W.scalarOneForm := by
          simpa only [hplus] using hgerm
        filter_upwards [hU, hbranch.eventuallyEq_nhds] with y hy heq
        have hobstruction :=
          B.plusObstruction_eq_zero_of_eventuallyEq_closed
            hopen hy W.scalarOneForm W.scalarClosed heq
        simpa [actualMetricScalarClosureObstruction4, hjet y] using hobstruction
      · have hbranch : B.plusField =ᶠ[nhds z]
            fun y => -W.scalarOneForm y := by
          simpa only [hplus] using hgerm
        filter_upwards [hU, hbranch.eventuallyEq_nhds] with y hy heq
        have hobstruction :=
          B.plusObstruction_eq_zero_of_eventuallyEq_closed
            hopen hy (fun y => -W.scalarOneForm y) hclosedNeg heq
        simpa [actualMetricScalarClosureObstruction4, hjet y] using hobstruction
  | true =>
      rcases hgerm with hgerm | hgerm
      · have hbranch : B.minusField =ᶠ[nhds z] W.scalarOneForm := by
          simpa only [hminus] using hgerm
        filter_upwards [hU, hbranch.eventuallyEq_nhds] with y hy heq
        have hobstruction :=
          B.minusObstruction_eq_zero_of_eventuallyEq_closed
            hopen hy W.scalarOneForm W.scalarClosed heq
        simpa [actualMetricScalarClosureObstruction4, hjet y] using hobstruction
      · have hbranch : B.minusField =ᶠ[nhds z]
            fun y => -W.scalarOneForm y := by
          simpa only [hminus] using hgerm
        filter_upwards [hU, hbranch.eventuallyEq_nhds] with y hy heq
        have hobstruction :=
          B.minusObstruction_eq_zero_of_eventuallyEq_closed
            hopen hy (fun y => -W.scalarOneForm y) hclosedNeg heq
        simpa [actualMetricScalarClosureObstruction4, hjet y] using hobstruction

/-- The local scalar selector simultaneously clears the literal closure and
Ricci-reconstruction gates for one finite raw detector choice. -/
theorem exists_actualMetricScalarClosureAndReconstructionChoice_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (base : ActualMetricDetectorChoice4) (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0) :
    ∃ selected : ActualMetricDetectorChoice4,
      selected.scalarTimelikeProbe = i ∧
      selected.scalarSpacelikeProbe = j ∧
      (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j
            selected.relativeMinus z) = W.scalarOneForm z ∨
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j
            selected.relativeMinus z) = -W.scalarOneForm z) ∧
      actualMetricScalarClosureObstruction4 g i j
        selected.relativeMinus z = 0 ∧
      actualMetricReconstructionObstruction4 g selected z = 0 ∧
      IsActualMetricMaxwellEntranceAt4 g selected z := by
  obtain ⟨relativeMinus, horbit, hclosure⟩ :=
    exists_actualMetricScalarOrbitAndClosureChoice_of_emdRicciWitnessPatch
      g B hopen hz i j hjet W halgebraic hprobeA hprobeB halpha hbeta
  let selected : ActualMetricDetectorChoice4 :=
    { base with
      scalarTimelikeProbe := i
      scalarSpacelikeProbe := j
      relativeMinus := relativeMinus }
  refine ⟨selected, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [selected] using horbit
  · exact hclosure
  · apply actualMetricReconstructionObstruction4_eq_zero_of_emdRicciWitness
      g z selected (W.witnessAt z hz) (W.scalarOneForm z)
      (W.scalarCovector_eq z hz) (halgebraic z hz)
    simpa [selected] using horbit
  · apply isActualMetricMaxwellEntranceAt4_of_emdRicciWitness
      g z selected (W.witnessAt z hz) (W.scalarOneForm z)
      (W.scalarCovector_eq z hz) (halgebraic z hz)
    simpa [selected] using horbit

@[simp] theorem isActualMetricMaxwellEntranceAt4_withMaxwellFrame
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4)
    (z : CurvatureCoordinateSpace4) :
    IsActualMetricMaxwellEntranceAt4 g
        (choice.withMaxwellFrame i j recipe k l) z ↔
      IsActualMetricMaxwellEntranceAt4 g choice z := by
  rfl

@[simp] theorem actualMetricReconstructionObstruction4_withMaxwellFrame
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (i j : Fin 4) (recipe : LorentzianPivotRecipe) (k l : Fin 4)
    (z : CurvatureCoordinateSpace4) :
    actualMetricReconstructionObstruction4 g
        (choice.withMaxwellFrame i j recipe k l) z =
      actualMetricReconstructionObstruction4 g choice z := by
  rfl

@[simp] theorem actualMetricReconstructionObstruction4_withOrientationReverse
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) (reverse : Bool)
    (z : CurvatureCoordinateSpace4) :
    actualMetricReconstructionObstruction4 g
        (choice.withOrientationReverse reverse) z =
      actualMetricReconstructionObstruction4 g choice z := by
  rfl

/-- **Germ-retaining upstream selector for the actual metric.** Starting from
the choice-independent EMD Ricci patch and one regular fixed scalar-probe
patch, the finite scalar, Maxwell-frame, and orientation selectors compose
to a single raw choice passing every metric-only upstream gate. The same
choice retains the locally fixed physical scalar sign and all four strict
Maxwell-frame signs on a neighborhood. -/
theorem exists_actualMetricUpstreamEntranceAt4_and_scalarFrameGerms_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (base : ActualMetricDetectorChoice4) (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hposA : 0 < 2 * (-1 : ℝ) * reconstructedDiagonalAField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hposB : 0 < 2 * (1 : ℝ) * reconstructedDiagonalBField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hg : ContinuousAt g z)
    (hP : ∀ choice a b, ContinuousAt
      (fun w => actualMetricMaxwellMinusProjectorCandidateField4
        g choice w a b) z)
    (hQ : ∀ choice a b, ContinuousAt
      (fun w => actualMetricMaxwellPlusProjectorCandidateField4
        g choice w a b) z)
    (hindex : HasLorentzianIndexOne
      (continuousBilinFormToBilin (g z))) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice.scalarTimelikeProbe = i ∧
      choice.scalarSpacelikeProbe = j ∧
      IsActualMetricUpstreamEntranceAt4 g z choice ∧
      (((fun y => oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z] W.scalarOneForm) ∨
        ((fun y => oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z]
              fun y => -W.scalarOneForm y)) ∧
      (∀ᶠ w in 𝓝 z,
        smoothMetricPairing g
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice) w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
              (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
              (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) w ∧
          0 < smoothMetricPairing g
            (actualMetricMaxwellPlusProbe0Field4 g choice)
            (actualMetricMaxwellPlusProbe0Field4 g choice) w ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellPlusProbe0Field4 g choice)
              (actualMetricMaxwellPlusProbe1Field4 g choice))
            (smoothMetricOrthogonalizeSecond g
              (actualMetricMaxwellPlusProbe0Field4 g choice)
              (actualMetricMaxwellPlusProbe1Field4 g choice)) w) := by
  obtain ⟨relativeMinus, hscalarGerm, hclosure⟩ :=
    exists_actualMetricScalarGermAndClosureChoice_of_emdRicciWitnessPatch
      g B hopen hz i j hjet W halgebraic hprobeA hprobeB halpha hbeta
  let scalarChoice : ActualMetricDetectorChoice4 :=
    { base with
      scalarTimelikeProbe := i
      scalarSpacelikeProbe := j
      relativeMinus := relativeMinus }
  have hi : scalarChoice.scalarTimelikeProbe = i := rfl
  have hj : scalarChoice.scalarSpacelikeProbe = j := rfl
  have horbit :
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j
            scalarChoice.relativeMinus z) = W.scalarOneForm z ∨
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j
            scalarChoice.relativeMinus z) = -W.scalarOneForm z := by
    rcases hscalarGerm with hscalarGerm | hscalarGerm
    · exact Or.inl (by simpa [scalarChoice] using hscalarGerm.self_of_nhds)
    · exact Or.inr (by simpa [scalarChoice] using hscalarGerm.self_of_nhds)
  have hreconstruction :
      actualMetricReconstructionObstruction4 g scalarChoice z = 0 := by
    apply actualMetricReconstructionObstruction4_eq_zero_of_emdRicciWitness
      g z scalarChoice (W.witnessAt z hz) (W.scalarOneForm z)
      (W.scalarCovector_eq z hz) (halgebraic z hz)
    simpa [hi, hj] using horbit
  have hmaxwell : IsActualMetricMaxwellEntranceAt4 g scalarChoice z := by
    apply isActualMetricMaxwellEntranceAt4_of_emdRicciWitness
      g z scalarChoice (W.witnessAt z hz) (W.scalarOneForm z)
      (W.scalarCovector_eq z hz) (halgebraic z hz)
    simpa [hi, hj] using horbit
  have halg := halgebraic z hz
  have halg' := halg
  unfold IsActualMetricAlgebraicEntranceAt4 at halg'
  dsimp only at halg'
  rcases halg' with
    ⟨hGsym, hdetG, _, _, _, _, hqSqPos, _⟩
  have hgsymm : (continuousBilinFormToBilin (g z)).IsSymm := by
    rw [← coordinateMetricMatrixField4_toBilin' g z]
    exact Matrix.isSymm_toBilin'_iff_isSymm.mpr hGsym
  have hresidual := actualMetricMaxwellResidual_toLin_eq_emdRicciWitness
    g z scalarChoice (W.witnessAt z hz) (W.scalarOneForm z)
    (W.scalarCovector_eq z hz) halg (by simpa [hi, hj] using horbit)
  have htrace : Matrix.trace
      (actualMetricMaxwellResidualCandidateField4 g scalarChoice z) = 0 := by
    rw [← Matrix.trace_toLin'_eq, hresidual,
      (W.witnessAt z hz).maxwellTrace]
  have henergy : HasPositiveMaxwellEnergyDensity
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin'
        (actualMetricMaxwellResidualCandidateField4 g scalarChoice z)) := by
    rw [hresidual]
    exact (W.witnessAt z hz).maxwellPositiveEnergy
  obtain ⟨m0, m1, recipe, p0, p1, hframesEventually⟩ :=
    exists_eventually_actualMetricMaxwellFrameChoice_of_positiveEnergy
      g scalarChoice z hg (hP scalarChoice) (hQ scalarChoice)
      hgsymm hindex hqSqPos htrace henergy hmaxwell
  let framed := scalarChoice.withMaxwellFrame m0 m1 recipe p0 p1
  have hframes :
      smoothMetricPairing g
          (actualMetricMaxwellLorentzPivotCandidateField4 g framed)
          (actualMetricMaxwellLorentzPivotCandidateField4 g framed) z < 0 ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g framed)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g framed))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g framed)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g framed)) z ∧
        0 < smoothMetricPairing g
          (actualMetricMaxwellPlusProbe0Field4 g framed)
          (actualMetricMaxwellPlusProbe0Field4 g framed) z ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g framed)
            (actualMetricMaxwellPlusProbe1Field4 g framed))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g framed)
            (actualMetricMaxwellPlusProbe1Field4 g framed)) z := by
    exact hframesEventually.self_of_nhds
  have hmaxwellFramed : IsActualMetricMaxwellEntranceAt4 g framed z := by
    exact (isActualMetricMaxwellEntranceAt4_withMaxwellFrame
      g scalarChoice m0 m1 recipe p0 p1 z).mpr hmaxwell
  obtain ⟨reverse, hhodge⟩ :=
    exists_actualMetricHodgeOrientationChoice_of_maxwellEntrance
      g framed z hgsymm hdetG hqSqPos hmaxwellFramed
      hframes.1 hframes.2.1 hframes.2.2.1 hframes.2.2.2
  let selected := framed.withOrientationReverse reverse
  refine ⟨selected, rfl, rfl, ?_, ?_, ?_⟩
  · unfold IsActualMetricUpstreamEntranceAt4
    dsimp only
    refine ⟨halg, hposA, hposB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [selected, framed, hi,
        ActualMetricDetectorChoice4.withOrientationReverse,
        ActualMetricDetectorChoice4.withMaxwellFrame,
        smoothMetricPairing, smoothMatrixProjectedVector,
        curvatureCoordinateDirection_eq_piBasisFun,
        Matrix.toLin'_apply, continuousBilinFormToBilin] using hprobeA z hz
    · simpa [selected, framed, hj,
        ActualMetricDetectorChoice4.withOrientationReverse,
        ActualMetricDetectorChoice4.withMaxwellFrame,
        smoothMetricPairing, smoothMatrixProjectedVector,
        curvatureCoordinateDirection_eq_piBasisFun,
        Matrix.toLin'_apply, continuousBilinFormToBilin] using hprobeB z hz
    · simpa [selected, framed, scalarChoice,
        ActualMetricDetectorChoice4.withOrientationReverse,
        ActualMetricDetectorChoice4.withMaxwellFrame] using hclosure
    · rw [show selected = framed.withOrientationReverse reverse by rfl,
        actualMetricReconstructionObstruction4_withOrientationReverse,
        show framed = scalarChoice.withMaxwellFrame m0 m1 recipe p0 p1 by rfl,
        actualMetricReconstructionObstruction4_withMaxwellFrame]
      exact hreconstruction
    · exact (isActualMetricMaxwellEntranceAt4_withOrientationReverse
        g framed reverse z).mpr hmaxwellFramed
    · exact hhodge
    · simpa [selected] using hframes.1
    · simpa [selected] using hframes.2.1
    · simpa [selected] using hframes.2.2.1
    · simpa [selected] using hframes.2.2.2
  · simpa [selected, framed, scalarChoice,
      ActualMetricDetectorChoice4.withOrientationReverse,
      ActualMetricDetectorChoice4.withMaxwellFrame] using hscalarGerm
  · simpa [selected] using hframesEventually

/-- **Fixed-choice upstream neighborhood promotion.**  Once a selected
pointwise upstream choice retains its scalar germ and four frame-sign germs,
the choice-independent EMD Ricci patch promotes that *same* finite choice to
the full upstream entrance on a smaller neighborhood.  The only additional
regularity used here is continuity of the two strict reconstructed diagonal
amplitudes and of the selected coframe entries.  Coframe continuity preserves
the positive orientation already certified by the exact base-point Hodge
gate; exact Hodge compatibility at nearby points is then re-derived from the
metric and Maxwell entrance, rather than treated as an open equality. -/
theorem eventually_isActualMetricUpstreamEntranceAt4_of_scalarFrameGerms
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (choice : ActualMetricDetectorChoice4)
    (hi : choice.scalarTimelikeProbe = i)
    (hj : choice.scalarSpacelikeProbe = j)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hscalarGerm :
      ((fun y => oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y)) =ᶠ[nhds z] W.scalarOneForm) ∨
      ((fun y => oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y)) =ᶠ[nhds z]
            fun y => -W.scalarOneForm y))
    (hframesGerm : ∀ᶠ y in nhds z,
      smoothMetricPairing g
          (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
          (actualMetricMaxwellLorentzPivotCandidateField4 g choice) y < 0 ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) y ∧
        0 < smoothMetricPairing g
          (actualMetricMaxwellPlusProbe0Field4 g choice)
          (actualMetricMaxwellPlusProbe0Field4 g choice) y ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g choice)
            (actualMetricMaxwellPlusProbe1Field4 g choice))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g choice)
            (actualMetricMaxwellPlusProbe1Field4 g choice)) y)
    (hdiagA : ContinuousAt (fun y =>
      2 * (-1 : ℝ) * reconstructedDiagonalAField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) y) z)
    (hdiagB : ContinuousAt (fun y =>
      2 * (1 : ℝ) * reconstructedDiagonalBField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) y) z)
    (hcoframe : ∀ r c, ContinuousAt (fun y =>
      actualMetricPrincipalCoframeCandidateField4 g choice y r c) z) :
    ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice := by
  have hdetAt : 0 < Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g choice z) :=
    actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
      g z choice hupstream
  have hupstream' := hupstream
  unfold IsActualMetricUpstreamEntranceAt4 at hupstream'
  dsimp only at hupstream'
  rcases hupstream' with
    ⟨_, hposA, hposB, _, _, _, _, _, _, _, _, _, _⟩
  have hposAEventually :=
    continuousAt_const.eventually_lt hdiagA hposA
  have hposBEventually :=
    continuousAt_const.eventually_lt hdiagB hposB
  have hcoframeContinuous : ContinuousAt
      (fun y => actualMetricPrincipalCoframeCandidateField4 g choice y) z :=
    continuousAt_pi.mpr fun r => continuousAt_pi.mpr fun c => hcoframe r c
  have hdetContinuous : ContinuousAt (fun y => Matrix.det
      (actualMetricPrincipalCoframeCandidateField4 g choice y)) z := by
    change ContinuousAt
      ((fun L : Matrix4 => Matrix.det L) ∘
        fun y => actualMetricPrincipalCoframeCandidateField4 g choice y) z
    exact continuous_id.matrix_det.continuousAt.comp hcoframeContinuous
  have hdetEventually :=
    continuousAt_const.eventually_lt hdetContinuous hdetAt
  have hscalarGermIJ :
      ((fun y => oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g i j
          choice.relativeMinus y)) =ᶠ[nhds z] W.scalarOneForm) ∨
      ((fun y => oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g i j
          choice.relativeMinus y)) =ᶠ[nhds z]
            fun y => -W.scalarOneForm y) := by
    simpa only [hi, hj] using hscalarGerm
  have hclosureEventually :=
    eventually_actualMetricScalarClosureObstruction4_eq_zero_of_germ
      g B hopen hz i j hjet W choice.relativeMinus hscalarGermIJ
  have horbitEventually : ∀ᶠ y in nhds z,
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = W.scalarOneForm y ∨
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = -W.scalarOneForm y := by
    rcases hscalarGerm with hscalarGerm | hscalarGerm
    · filter_upwards [hscalarGerm] with y hy
      exact Or.inl hy
    · filter_upwards [hscalarGerm] with y hy
      exact Or.inr hy
  filter_upwards [hopen.mem_nhds hz, hposAEventually, hposBEventually,
      hframesGerm, hdetEventually, hclosureEventually, horbitEventually]
      with y hyU hposAy hposBy hframesY hdetY hclosureY horbitY
  have halg := halgebraic y hyU
  have hreconstruction :
      actualMetricReconstructionObstruction4 g choice y = 0 := by
    exact actualMetricReconstructionObstruction4_eq_zero_of_emdRicciWitness
      g y choice (W.witnessAt y hyU) (W.scalarOneForm y)
        (W.scalarCovector_eq y hyU) halg horbitY
  have hmaxwell : IsActualMetricMaxwellEntranceAt4 g choice y := by
    exact isActualMetricMaxwellEntranceAt4_of_emdRicciWitness
      g y choice (W.witnessAt y hyU) (W.scalarOneForm y)
        (W.scalarCovector_eq y hyU) halg horbitY
  have halg' := halg
  unfold IsActualMetricAlgebraicEntranceAt4 at halg'
  dsimp only at halg'
  rcases halg' with
    ⟨hGsym, _, _, _, _, _, hqSqPos, _⟩
  have hgsymm : (continuousBilinFormToBilin (g y)).IsSymm := by
    rw [← coordinateMetricMatrixField4_toBilin' g y]
    exact Matrix.isSymm_toBilin'_iff_isSymm.mpr hGsym
  have hhodge : IsActualMetricHodgeCompatibleAt4 g choice y :=
    isActualMetricHodgeCompatibleAt4_of_maxwellEntrance_det_pos
      g choice y hgsymm hqSqPos hmaxwell hframesY.1
        hframesY.2.1 hframesY.2.2.1 hframesY.2.2.2 hdetY
  refine ⟨hyU, ?_⟩
  unfold IsActualMetricUpstreamEntranceAt4
  dsimp only
  refine ⟨halg, hposAy, hposBy, ?_, ?_, ?_, hreconstruction,
    hmaxwell, hhodge, hframesY.1, hframesY.2.1,
    hframesY.2.2.1, hframesY.2.2.2⟩
  · simpa [hi, smoothMetricPairing, smoothMatrixProjectedVector,
      curvatureCoordinateDirection_eq_piBasisFun,
      Matrix.toLin'_apply, continuousBilinFormToBilin] using hprobeA y hyU
  · simpa [hj, smoothMetricPairing, smoothMatrixProjectedVector,
      curvatureCoordinateDirection_eq_piBasisFun,
      Matrix.toLin'_apply, continuousBilinFormToBilin] using hprobeB y hyU
  · simpa only [hi, hj] using hclosureY

/-- **Selected fixed-choice upstream patch.**  The finite scalar, Maxwell
frame, and orientation selectors can be performed once at `z` and the
resulting raw choice reused on a whole smaller neighborhood.  In particular,
the selected coframe has positive determinant there and hence carries the
same exact (not merely up-to-sign) Hodge convention throughout the patch. -/
theorem exists_eventually_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (base : ActualMetricDetectorChoice4) (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hposA : 0 < 2 * (-1 : ℝ) * reconstructedDiagonalAField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hposB : 0 < 2 * (1 : ℝ) * reconstructedDiagonalBField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hg : ContinuousAt g z)
    (hP : ∀ choice a b, ContinuousAt
      (fun w => actualMetricMaxwellMinusProjectorCandidateField4
        g choice w a b) z)
    (hQ : ∀ choice a b, ContinuousAt
      (fun w => actualMetricMaxwellPlusProjectorCandidateField4
        g choice w a b) z)
    (hindex : HasLorentzianIndexOne
      (continuousBilinFormToBilin (g z)))
    (hdiagA : ContinuousAt (fun y =>
      2 * (-1 : ℝ) * reconstructedDiagonalAField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) y) z)
    (hdiagB : ContinuousAt (fun y =>
      2 * (1 : ℝ) * reconstructedDiagonalBField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) y) z)
    (hcoframe : ∀ choice r c, ContinuousAt (fun y =>
      actualMetricPrincipalCoframeCandidateField4 g choice y r c) z) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice.scalarTimelikeProbe = i ∧
      choice.scalarSpacelikeProbe = j ∧
      (((fun y => oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z] W.scalarOneForm) ∨
        ((fun y => oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z]
              fun y => -W.scalarOneForm y)) ∧
      (∀ᶠ y in nhds z,
        y ∈ U ∧
        0 < Matrix.det
          (actualMetricPrincipalCoframeCandidateField4 g choice y) ∧
        IsActualMetricUpstreamEntranceAt4 g y choice) := by
  obtain ⟨choice, hi, hj, hupstream, hscalarGerm, hframesGerm⟩ :=
    exists_actualMetricUpstreamEntranceAt4_and_scalarFrameGerms_of_emdRicciWitnessPatch
      g B hopen hz base i j hjet W halgebraic hprobeA hprobeB
        halpha hbeta hposA hposB hg hP hQ hindex
  have heventually :=
    eventually_isActualMetricUpstreamEntranceAt4_of_scalarFrameGerms
      g B hopen hz i j hjet W halgebraic hprobeA hprobeB choice hi hj
        hupstream hscalarGerm hframesGerm hdiagA hdiagB (hcoframe choice)
  refine ⟨choice, hi, hj, hscalarGerm, ?_⟩
  filter_upwards [heventually] with y hy
  exact ⟨hy.1,
    actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
      g y choice hy.2,
    hy.2⟩

/-- Eventual fixed-choice upstream entrance can be represented by an honest
open patch contained in the original physical domain. -/
theorem exists_open_actualMetricUpstreamPatch_of_eventually
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice) :
    ∃ V : Set CurvatureCoordinateSpace4,
      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, IsActualMetricUpstreamEntranceAt4 g y choice := by
  have hmem : {y | y ∈ U ∧
      IsActualMetricUpstreamEntranceAt4 g y choice} ∈ nhds z :=
    hupstream
  obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hmem
  refine ⟨V, hVopen, hzV, ?_, ?_⟩
  · intro y hy
    exact (hVsub hy).1
  · intro y hy
    exact (hVsub hy).2

/-- Existential-choice interface for downstream patchwise composition. -/
theorem exists_choice_open_actualMetricUpstreamPatch_of_eventually
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hselected : ∃ choice : ActualMetricDetectorChoice4,
      ∀ᶠ y in nhds z,
        y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice) :
    ∃ choice : ActualMetricDetectorChoice4,
      ∃ V : Set CurvatureCoordinateSpace4,
        IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        ∀ y ∈ V, IsActualMetricUpstreamEntranceAt4 g y choice := by
  obtain ⟨choice, hupstream⟩ := hselected
  obtain ⟨V, hVopen, hzV, hVU, hupstreamV⟩ :=
    exists_open_actualMetricUpstreamPatch_of_eventually
      g choice z hupstream
  exact ⟨choice, V, hVopen, hzV, hVU, hupstreamV⟩

/-- **Upstream selector composition for the actual metric.** This is the
pointwise projection of the germ-retaining selector above, kept as the stable
interface for downstream detector theorems. -/
theorem exists_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (base : ActualMetricDetectorChoice4) (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let P := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (P ((Pi.basisFun ℝ (Fin 4)) i))
        (P ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Q := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Q ((Pi.basisFun ℝ (Fin 4)) j))
        (Q ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hposA : 0 < 2 * (-1 : ℝ) * reconstructedDiagonalAField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hposB : 0 < 2 * (1 : ℝ) * reconstructedDiagonalBField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hg : ContinuousAt g z)
    (hP : ∀ choice a b, ContinuousAt
      (fun w => actualMetricMaxwellMinusProjectorCandidateField4
        g choice w a b) z)
    (hQ : ∀ choice a b, ContinuousAt
      (fun w => actualMetricMaxwellPlusProjectorCandidateField4
        g choice w a b) z)
    (hindex : HasLorentzianIndexOne
      (continuousBilinFormToBilin (g z))) :
    ∃ choice : ActualMetricDetectorChoice4,
      IsActualMetricUpstreamEntranceAt4 g z choice := by
  obtain ⟨choice, _, _, hupstream, _, _⟩ :=
    exists_actualMetricUpstreamEntranceAt4_and_scalarFrameGerms_of_emdRicciWitnessPatch
      g B hopen hz base i j hjet W halgebraic hprobeA hprobeB halpha hbeta
      hposA hposB hg hP hQ hindex
  exact ⟨choice, hupstream⟩

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- Legacy universal-premise composition theorem.  This implication is kept
only as a low-level logical convenience: its universal `hgeneric` premise is
too strong for the finite detector, which deliberately enumerates rejected
diagonal wedge choices.  The publication route uses existential channel
selection from `IsActualMetricActiveFourthOrderWedgeAt` instead. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) (a : ℝ)
    (hupstream : ∃ rawChoice : ActualMetricDetectorChoice4,
      IsActualMetricUpstreamEntranceAt4 g z rawChoice)
    (hEMD : ∀ rawChoice, IsActualMetricUpstreamEntranceAt4 g z rawChoice →
      IsActualMetricConstantCouplingEMDRealizationAt g z rawChoice a)
    (hgeneric : ∀ rawChoice, IsActualMetricUpstreamEntranceAt4 g z rawChoice →
      IsActualMetricGenericFourthOrderComponentAt g z rawChoice) :
    ∃ rawChoice : ActualMetricDetectorChoice4,
      rawChoice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z rawChoice = a ^ 2 := by
  obtain ⟨rawChoice, hchoice⟩ := hupstream
  refine ⟨rawChoice, ?_, ?_⟩
  · exact mem_acceptedActualMetricFourthOrderDetectorChoicesAt_of_upstream_emdRealization
      g z rawChoice a hchoice (hEMD rawChoice hchoice) (hgeneric rawChoice hchoice)
  · exact actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_upstream_emdRealization
      g z rawChoice a hchoice (hEMD rawChoice hchoice) (hgeneric rawChoice hchoice)

/-- Legacy Kaluza specialization of the universal-premise composition
theorem.  Use the active-wedge/existential-channel route for nonvacuous
geometric necessity. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) (a : ℝ)
    (hupstream : ∃ rawChoice : ActualMetricDetectorChoice4,
      IsActualMetricUpstreamEntranceAt4 g z rawChoice)
    (hEMD : ∀ rawChoice, IsActualMetricUpstreamEntranceAt4 g z rawChoice →
      IsActualMetricConstantCouplingEMDRealizationAt g z rawChoice a)
    (hgeneric : ∀ rawChoice, IsActualMetricUpstreamEntranceAt4 g z rawChoice →
      IsActualMetricGenericFourthOrderComponentAt g z rawChoice)
    (hKaluza : a ^ 2 = 3) :
    ∃ rawChoice : ActualMetricDetectorChoice4,
      rawChoice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z rawChoice = 3 := by
  obtain ⟨rawChoice, hmem, hout⟩ :=
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_upstream
      g z a hupstream hEMD hgeneric
  exact ⟨rawChoice, hmem, hout.trans hKaluza⟩

/-- **Geometric scalar identifiability from a choice-independent EMD Ricci
witness.** On the stated generic branch, a genuine physical Ricci
decomposition forces the finite, metric-only polynomial-projector search to
contain the physical scalar covector, up to its unavoidable global sign.

The reconstruction equation is not assumed: it is derived here from the
rank-one Ricci decomposition and Maxwell square law. -/
theorem exists_actualMetricFiniteProbeScalarBranch_eq_or_neg_of_emdRicciWitness
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessAt4 g z)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g z)
    (hcausal : IsActualMetricScalarEigenlineCausalAt4 g z) :
    ∃ i j : Fin 4, ∃ relativeMinus : Bool,
      (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          W.scalarCovector ∨
        (oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g i j relativeMinus z)).toLinearMap =
          -W.scalarCovector := by
  have hrecon := reconstructionEquation_of_rankOneRicciDecomposition
    (Matrix.toLin' (actualMixedRicciField4 g z)) W.maxwellRicci
    W.scalarCovector W.scalarVector
    (actualRicciComplementaryRootAField4 g z +
      actualRicciComplementaryRootBField4 g z)
    (actualRicciReconstructedQSqField4 g z)
    W.ricciDecomposition W.maxwellSquare W.scalarTrace
  exact
    exists_actualMetricFiniteProbeScalarBranch_eq_or_neg_of_physicalCovector
      g z W.scalarCovector W.scalarVector W.ricciEigenbasis W.orthonormal
      W.eigenA W.eigenMinus W.eigenB W.eigenPlus W.metricDual
      W.minusNonresonance W.plusNonresonance hrecon halgebraic hcausal

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
