import RainichKaluza.PhaseIIIRescaledSeedRealization

set_option maxSynthPendingDepth 2

/-!
# Calculus realization of the transported Phase-III seed

This file discharges the two coordinate-jet hypotheses isolated by
`PositiveQPhaseIIISeedPairC1Realization.ofSmoothCoordinateJets`.  The proof is
entrywise, so it does not require a noncanonical norm on `Matrix4`:

* `sqrt (2q)` has the displayed positive-branch derivative;
* finite scalar product rules differentiate `Lᵀ F L`;
* the resulting coordinate derivative is exactly the algebraic transported
  seed jet already used by the Phase-III exterior obstruction;
* `C²` regularity makes these actual first jets continuous.

Thus actual coordinate derivatives of `L` and `q` now suffice to construct the
constituent seed-pair realization consumed by the physical Maxwell-field
theorem.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

@[simp]
theorem oneForm4ContinuousLinearMap_curvatureCoordinateDirection
    (v : OneForm4) (i : Fin 4) :
    oneForm4ContinuousLinearMap v (curvatureCoordinateDirection i) = v i := by
  simp [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    curvatureCoordinateDirection, eq_comm]

/-- Continuous linear maps on four-space are equal when they agree on the
four coordinate directions.  Using the explicit basis expansion avoids
instance-coherence problems caused by unfolding the reducible coordinate
space abbreviation. -/
theorem continuousLinearMap_ext_curvatureCoordinateDirection
    {A B : CurvatureCoordinateSpace4 →L[ℝ] ℝ}
    (h : ∀ k, A (curvatureCoordinateDirection k) =
      B (curvatureCoordinateDirection k)) : A = B := by
  apply ContinuousLinearMap.ext
  intro u
  conv_lhs => rw [← curvatureCoordinateDirection_expansion u]
  conv_rhs => rw [← curvatureCoordinateDirection_expansion u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [h k]

/-- A differentiable scalar field has the continuous-linear derivative
specified by its four coordinate components. -/
theorem hasFDerivAt_of_coordinateFDeriv
    (f : CurvatureCoordinateSpace4 → ℝ) (D : OneForm4)
    (z : CurvatureCoordinateSpace4)
    (hf : DifferentiableAt ℝ f z)
    (hD : scalarFieldCoordinateFDeriv f z = D) :
    HasFDerivAt f (oneForm4ContinuousLinearMap D) z := by
  apply hf.hasFDerivAt.congr_fderiv
  ext u
  rw [scalarField_fderiv_eq_coordinateEvaluation, hD]
  rfl

/-- The positive amplitude `sqrt (2q)` has the exact derivative used in the
canonical Phase-III seed jet. -/
theorem hasFDerivAt_sqrt_two_mul
    (q : CurvatureCoordinateSpace4 → ℝ)
    (dq : OneForm4) (z : CurvatureCoordinateSpace4)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) :
    HasFDerivAt (fun y => Real.sqrt (2 * q y))
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k))) z := by
  have hsqrt := (hq.const_mul 2).sqrt (by positivity)
  have hderiv :
      (1 / (2 * Real.sqrt (2 * q z))) •
          ((2 : ℝ) • oneForm4ContinuousLinearMap dq) =
        oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k)) := by
    apply continuousLinearMap_ext_curvatureCoordinateDirection
    intro k
    simp only [smul_apply,
      oneForm4ContinuousLinearMap_curvatureCoordinateDirection, smul_eq_mul]
    unfold canonicalPositiveQAmplitudeDerivative
    have hsqrt0 : Real.sqrt (2 * q z) ≠ 0 := by positivity
    field_simp [hsqrt0]
  exact hsqrt.congr_fderiv hderiv

/-- Entrywise derivative of the canonical positive-`q` electric seed. -/
theorem hasFDerivAt_smoothCanonicalPositiveQSeed_entry
    (q : CurvatureCoordinateSpace4 → ℝ)
    (dq : OneForm4) (z : CurvatureCoordinateSpace4)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    HasFDerivAt (fun y => smoothCanonicalPositiveQSeed q y i j)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQSeedDerivative (q z) (dq k) i j)) z := by
  have hamp := hasFDerivAt_sqrt_two_mul q dq z hq hqPos
  let eij := canonicalMaxwellTwoForm 1 0 i j
  have hfun : (fun y => smoothCanonicalPositiveQSeed q y i j) =
      fun y => Real.sqrt (2 * q y) * eij := by
    funext y
    dsimp only [eij]
    fin_cases i <;> fin_cases j <;>
      simp [smoothCanonicalPositiveQSeed, canonicalMaxwellTwoForm]
  have hderiv :
      oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQSeedDerivative (q z) (dq k) i j) =
        eij • oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k)) := by
    have hentry (k : Fin 4) :
        canonicalPositiveQSeedDerivative (q z) (dq k) i j =
          canonicalPositiveQAmplitudeDerivative (q z) (dq k) * eij := by
      dsimp only [eij]
      fin_cases i <;> fin_cases j <;>
        simp [canonicalPositiveQSeedDerivative, canonicalMaxwellTwoForm]
    ext u
    simp only [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
      smul_apply, smul_eq_mul]
    simp_rw [hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun, hderiv]
  exact hamp.mul_const eij

/-- Entrywise derivative of the canonical positive-`q` Hodge seed. -/
theorem hasFDerivAt_smoothCanonicalPositiveQHodgeSeed_entry
    (q : CurvatureCoordinateSpace4 → ℝ)
    (dq : OneForm4) (z : CurvatureCoordinateSpace4)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    HasFDerivAt (fun y => smoothCanonicalPositiveQHodgeSeed q y i j)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQHodgeSeedDerivative (q z) (dq k) i j)) z := by
  have hamp := hasFDerivAt_sqrt_two_mul q dq z hq hqPos
  let eij := canonicalHodgeStar 1 0 i j
  have hfun : (fun y => smoothCanonicalPositiveQHodgeSeed q y i j) =
      fun y => Real.sqrt (2 * q y) * eij := by
    funext y
    dsimp only [eij]
    fin_cases i <;> fin_cases j <;>
      simp [smoothCanonicalPositiveQHodgeSeed, canonicalHodgeStar,
        canonicalMaxwellTwoForm]
  have hderiv :
      oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQHodgeSeedDerivative (q z) (dq k) i j) =
        eij • oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k)) := by
    have hentry (k : Fin 4) :
        canonicalPositiveQHodgeSeedDerivative (q z) (dq k) i j =
          canonicalPositiveQAmplitudeDerivative (q z) (dq k) * eij := by
      dsimp only [eij]
      fin_cases i <;> fin_cases j <;>
        simp [canonicalPositiveQHodgeSeedDerivative, canonicalHodgeStar,
          canonicalMaxwellTwoForm]
    ext u
    simp only [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
      smul_apply, smul_eq_mul]
    simp_rw [hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun, hderiv]
  exact hamp.mul_const eij

/-- The scalar-entry product rule for a transported two-form.  This is the
calculus counterpart of `transportedTwoFormDerivative`. -/
theorem hasFDerivAt_transportTwoForm_entry
    (L F : CurvatureCoordinateSpace4 → Matrix4)
    (dL dF : Fin 4 → Matrix4) (z : CurvatureCoordinateSpace4)
    (hL : ∀ i j, HasFDerivAt (fun y => L y i j)
      (oneForm4ContinuousLinearMap (fun k => dL k i j)) z)
    (hF : ∀ i j, HasFDerivAt (fun y => F y i j)
      (oneForm4ContinuousLinearMap (fun k => dF k i j)) z)
    (i j : Fin 4) :
    HasFDerivAt (fun y => transportTwoForm (L y) (F y) i j)
      (oneForm4ContinuousLinearMap
        (fun k => transportedTwoFormDerivative (L z) (dL k)
          (F z) (dF k) i j)) z := by
  let Dsum : CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
    ∑ b, ∑ a, (
      (L z a i * F z a b) •
          oneForm4ContinuousLinearMap (fun k => dL k b j) +
        L z b j •
          (L z a i • oneForm4ContinuousLinearMap (fun k => dF k a b) +
            F z a b • oneForm4ContinuousLinearMap (fun k => dL k a i)))
  have hsum : HasFDerivAt
      (fun y => ∑ b, ∑ a, (L y a i * F y a b) * L y b j)
      Dsum z := by
    dsimp only [Dsum]
    exact HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
        ((hL a i).mul (hF a b)).mul (hL b j)))
  have hfun : (fun y => transportTwoForm (L y) (F y) i j) =
      fun y => ∑ b, ∑ a, (L y a i * F y a b) * L y b j := by
    funext y
    simp only [transportTwoForm, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul]
  have hderiv : oneForm4ContinuousLinearMap
        (fun k => transportedTwoFormDerivative (L z) (dL k)
          (F z) (dF k) i j) = Dsum := by
    have hentry (k : Fin 4) :
        transportedTwoFormDerivative (L z) (dL k) (F z) (dF k) i j =
          ∑ b, ∑ a,
            ((L z a i * F z a b) * dL k b j +
              L z b j * (L z a i * dF k a b + F z a b * dL k a i)) := by
      calc
        transportedTwoFormDerivative (L z) (dL k) (F z) (dF k) i j =
            (∑ b, ∑ a, dL k a i * F z a b * L z b j) +
            (∑ b, ∑ a, L z a i * dF k a b * L z b j) +
            (∑ b, ∑ a, L z a i * F z a b * dL k b j) := by
          simp only [transportedTwoFormDerivative, Matrix.add_apply,
            Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        _ = ∑ b, ∑ a,
            ((L z a i * F z a b) * dL k b j +
              L z b j *
                (L z a i * dF k a b + F z a b * dL k a i)) := by
          simp only [mul_add, Finset.sum_add_distrib]
          have hframe :
              (∑ b, ∑ a, dL k a i * F z a b * L z b j) =
                ∑ b, ∑ a, L z b j * F z a b * dL k a i := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            ring
          have hamplitude :
              (∑ b, ∑ a, L z a i * dF k a b * L z b j) =
                ∑ b, ∑ a, L z b j * L z a i * dF k a b := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            ring
          rw [hframe, hamplitude]
          simp only [mul_assoc]
          abel
    apply continuousLinearMap_ext_curvatureCoordinateDirection
    intro k
    rw [oneForm4ContinuousLinearMap_curvatureCoordinateDirection]
    dsimp only [Dsum]
    simp only [sum_apply, add_apply, smul_apply,
      oneForm4ContinuousLinearMap_curvatureCoordinateDirection, smul_eq_mul]
    rw [hentry]
  rw [hfun, hderiv]
  exact hsum

/-- The displayed electric transported-seed jet is the actual coordinate
Fréchet derivative once `dL,dq` are the actual coordinate derivatives. -/
theorem smoothTransportedPositiveQSeed_coordinateFDeriv_eq
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (dL : Fin 4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ) (dq : OneForm4)
    (z : CurvatureCoordinateSpace4)
    (hL : ∀ i j, HasFDerivAt (fun y => L y i j)
      (oneForm4ContinuousLinearMap (fun k => dL k i j)) z)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => smoothTransportedPositiveQSeed L q y i j) z =
      fun k => localPositiveQSeedFirstDerivative (L z) dL (q z) dq k i j := by
  have hcanonical : ∀ a b, HasFDerivAt
      (fun y => smoothCanonicalPositiveQSeed q y a b)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQSeedDerivative (q z) (dq k) a b)) z :=
    fun a b => hasFDerivAt_smoothCanonicalPositiveQSeed_entry
      q dq z hq hqPos a b
  have htransport := hasFDerivAt_transportTwoForm_entry
    L (smoothCanonicalPositiveQSeed q) dL
      (fun k => canonicalPositiveQSeedDerivative (q z) (dq k))
    z hL hcanonical i j
  change scalarFieldCoordinateFDeriv
      (fun y => transportTwoForm (L y)
        (smoothCanonicalPositiveQSeed q y) i j) z = _
  funext k
  have happly := congrArg
    (fun A : CurvatureCoordinateSpace4 →L[ℝ] ℝ =>
      A (curvatureCoordinateDirection k)) htransport.fderiv
  simpa only [scalarFieldCoordinateFDeriv,
    oneForm4ContinuousLinearMap_curvatureCoordinateDirection,
    localPositiveQSeedFirstDerivative,
    transportedPositiveQSeedDerivative,
    smoothCanonicalPositiveQSeed] using happly

/-- The displayed Hodge transported-seed jet is likewise the actual
coordinate Fréchet derivative. -/
theorem smoothTransportedPositiveQHodgeSeed_coordinateFDeriv_eq
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (dL : Fin 4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ) (dq : OneForm4)
    (z : CurvatureCoordinateSpace4)
    (hL : ∀ i j, HasFDerivAt (fun y => L y i j)
      (oneForm4ContinuousLinearMap (fun k => dL k i j)) z)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => transportedPositiveQHodgeSeed (L y) (q y) i j) z =
      fun k => localPositiveQHodgeSeedFirstDerivative
        (L z) dL (q z) dq k i j := by
  have hcanonical : ∀ a b, HasFDerivAt
      (fun y => smoothCanonicalPositiveQHodgeSeed q y a b)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQHodgeSeedDerivative
          (q z) (dq k) a b)) z :=
    fun a b => hasFDerivAt_smoothCanonicalPositiveQHodgeSeed_entry
      q dq z hq hqPos a b
  have htransport := hasFDerivAt_transportTwoForm_entry
    L (smoothCanonicalPositiveQHodgeSeed q) dL
      (fun k => canonicalPositiveQHodgeSeedDerivative (q z) (dq k))
    z hL hcanonical i j
  change scalarFieldCoordinateFDeriv
      (fun y => transportTwoForm (L y)
        (smoothCanonicalPositiveQHodgeSeed q y) i j) z = _
  funext k
  have happly := congrArg
    (fun A : CurvatureCoordinateSpace4 →L[ℝ] ℝ =>
      A (curvatureCoordinateDirection k)) htransport.fderiv
  simpa only [scalarFieldCoordinateFDeriv,
    oneForm4ContinuousLinearMap_curvatureCoordinateDirection,
    localPositiveQHodgeSeedFirstDerivative,
    transportedPositiveQHodgeSeedDerivative,
    smoothCanonicalPositiveQHodgeSeed] using happly

namespace PositiveQPhaseIIISeedPairC1Realization

variable {U : Set CurvatureCoordinateSpace4}

/-- **Concrete transported-seed realization.**  If `L,q` are `C²` and the
stored arrays `dL,dq` are their actual coordinate derivatives, then both
transported seeds have exactly the first jets used by the Phase-III
obstruction.  Their jet continuity follows from the continuity of the actual
Fréchet derivative, eliminating all independent seed-jet hypotheses. -/
noncomputable def ofSmoothFrameMagnitude
    (M : PositiveQPhaseIIIPatch4 U)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PositiveQPhaseIIISeedPairC1Realization M := by
  have hseedSmooth : MatrixFieldContDiffOn 2 U
      (fun z => (M.exteriorJet z).F0) := by
    change MatrixFieldContDiffOn 2 U
      (smoothTransportedPositiveQSeed M.L M.q)
    exact contDiffOn_smoothTransportedPositiveQSeed hL hq hqPos
  have hhodgeSmooth : MatrixFieldContDiffOn 2 U
      (fun z => (M.exteriorJet z).G0) := by
    simpa only [PositiveQPhaseIIIPatch4.exteriorJet,
      localPositiveQExteriorDualityJet] using
      (contDiffOn_transportedPositiveQHodgeSeed hL hq hqPos)
  have hseedJet : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv
          (fun y => (M.exteriorJet y).F0 i j) z =
        fun k => M.seedFirstJet z k i j := by
    intro z hz i j
    have hLz : ∀ a b, HasFDerivAt (fun y => M.L y a b)
        (oneForm4ContinuousLinearMap (fun k => M.dL z k a b)) z := by
      intro a b
      exact hasFDerivAt_of_coordinateFDeriv _ _ z
        ((((hL a b).of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdL z hz a b)
    have hqz : HasFDerivAt M.q
        (oneForm4ContinuousLinearMap (M.dq z)) z :=
      hasFDerivAt_of_coordinateFDeriv _ _ z
        (((hq.of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdq z hz)
    change scalarFieldCoordinateFDeriv
        (fun y => smoothTransportedPositiveQSeed M.L M.q y i j) z = _
    exact smoothTransportedPositiveQSeed_coordinateFDeriv_eq
      M.L (M.dL z) M.q (M.dq z) z hLz hqz (hqPos z hz) i j
  have hhodgeSeedJet : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv
          (fun y => (M.exteriorJet y).G0 i j) z =
        fun k => M.hodgeSeedFirstJet z k i j := by
    intro z hz i j
    have hLz : ∀ a b, HasFDerivAt (fun y => M.L y a b)
        (oneForm4ContinuousLinearMap (fun k => M.dL z k a b)) z := by
      intro a b
      exact hasFDerivAt_of_coordinateFDeriv _ _ z
        ((((hL a b).of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdL z hz a b)
    have hqz : HasFDerivAt M.q
        (oneForm4ContinuousLinearMap (M.dq z)) z :=
      hasFDerivAt_of_coordinateFDeriv _ _ z
        (((hq.of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdq z hz)
    change scalarFieldCoordinateFDeriv
        (fun y => transportedPositiveQHodgeSeed (M.L y) (M.q y) i j) z = _
    exact smoothTransportedPositiveQHodgeSeed_coordinateFDeriv_eq
      M.L (M.dL z) M.q (M.dq z) z hLz hqz (hqPos z hz) i j
  have hseedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.seedFirstJet z k i j) U := by
    intro k i j
    have hderiv : ContinuousOn
        (fderiv ℝ (fun z => (M.exteriorJet z).F0 i j)) U :=
      (hseedSmooth i j).continuousOn_fderiv_of_isOpen hopen (by norm_num)
    have happly := continuousOn_clm_apply.mp hderiv (coordinateDirection k)
    exact happly.congr (fun z hz => (congrFun (hseedJet z hz i j) k).symm)
  have hhodgeSeedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.hodgeSeedFirstJet z k i j) U := by
    intro k i j
    have hderiv : ContinuousOn
        (fderiv ℝ (fun z => (M.exteriorJet z).G0 i j)) U :=
      (hhodgeSmooth i j).continuousOn_fderiv_of_isOpen hopen (by norm_num)
    have happly := continuousOn_clm_apply.mp hderiv (coordinateDirection k)
    exact happly.congr
      (fun z hz => (congrFun (hhodgeSeedJet z hz i j) k).symm)
  exact ofSmoothCoordinateJets M hopen (fun i j => (hL i j).of_le (by norm_num))
    (hq.of_le (by norm_num)) hqPos hseedJet hhodgeSeedJet
    hseedJetContinuous hhodgeSeedJetContinuous hc hs hdc hds

/-- The concrete calculus realization immediately supplies the precise
rescaled Maxwell realization consumed by the accepted-branch theorem. -/
noncomputable def rescaledOfSmoothFrameMagnitude
    (M : PositiveQPhaseIIIPatch4 U)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PositiveQPhaseIIIRescaledMaxwellC1Realization M :=
  (ofSmoothFrameMagnitude M hopen hL hq hqPos hdL hdq
    hc hs hdc hds).toRescaledMaxwellC1Realization

end PositiveQPhaseIIISeedPairC1Realization

namespace PhaseIIIAcceptedBranch

variable {U : Set CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- **Smooth seed to closed physical Maxwell field.**  An accepted Phase-III
branch, actual `C²` frame/magnitude fields, their displayed coordinate jets,
and actual `C¹` complexion coefficients canonically produce the matching
closed physical Maxwell field.  This composes the transported-seed calculus,
duality product rule, and exponential unweighting with no residual Maxwell
field-realization hypothesis. -/
noncomputable def toPhysicalMaxwellC1Realization_ofSmoothFrameMagnitude
    (A : PhaseIIIAcceptedBranch C M branch)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PhaseIIIPhysicalMaxwellC1Realization C M branch :=
  A.toPhysicalMaxwellC1Realization
    (PositiveQPhaseIIISeedPairC1Realization.rescaledOfSmoothFrameMagnitude
      M hopen hL hq hqPos hdL hdq hc hs hdc hds)
    hopen hstar

end PhaseIIIAcceptedBranch

end RainichKaluza
