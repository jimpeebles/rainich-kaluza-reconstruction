import RainichKaluza.FourthOrderMetricDetector

/-!
# Frame-invariant active-wedge locus

The fourth-order coupling detector is generic where the effective complexion
one-form is not parallel to the principal reflection of the scalar covector.
The detector writes this condition in a selected Maxwell principal coframe.
This file isolates its coordinate-invariant algebraic content.

For a mixed Maxwell stress endomorphism `S`, its natural action on covectors
is `S^T`.  If a coframe conjugates `S` to the canonical Maxwell residual
`diag(-q,-q,q,q)`, then pulling this cotangent action into the principal
frame gives `q` times `canonicalPrincipalReflectionCovector`.  Since `q` is
nonzero on the non-null branch, the existence of a nonzero wedge component
is therefore independent of the selected frame and of scalar orientation.
-/

namespace RainichKaluza

/-- The natural cotangent action of a mixed endomorphism.  In matrix
notation this is `S^T v`; it is intentionally left unnormalized so the
physical active predicate below needs only the mixed stress itself. -/
noncomputable def mixedEndomorphismCovectorAction
    (S : Matrix4) (v : OneForm4) : OneForm4 :=
  pullCovectorToPrincipalFrame S v

/-- Pulling covectors successively by `B` and then `A` is pullback by
`B * A`. -/
theorem pullCovectorToPrincipalFrame_comp
    (A B : Matrix4) (v : OneForm4) :
    pullCovectorToPrincipalFrame A
        (pullCovectorToPrincipalFrame B v) =
      pullCovectorToPrincipalFrame (B * A) v := by
  funext a
  simp [pullCovectorToPrincipalFrame, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- The identity matrix acts trivially on covectors. -/
@[simp] theorem pullCovectorToPrincipalFrame_one (v : OneForm4) :
    pullCovectorToPrincipalFrame (1 : Matrix4) v = v := by
  funext i
  fin_cases i <;>
    norm_num [pullCovectorToPrincipalFrame, Fin.sum_univ_succ,
      Matrix.one_apply]

/-- The canonical mixed Maxwell residual acts on covectors as `q` times the
canonical principal reflection. -/
theorem mixedEndomorphismCovectorAction_canonicalMaxwellResidual
    (q : ℝ) (v : OneForm4) :
    mixedEndomorphismCovectorAction (canonicalMaxwellResidual q) v =
      q • canonicalPrincipalReflectionCovector v := by
  funext i
  fin_cases i <;>
    simp [mixedEndomorphismCovectorAction, pullCovectorToPrincipalFrame,
      canonicalMaxwellResidual, canonicalPrincipalReflectionCovector,
      Fin.sum_univ_succ]

/-- **Cotangent naturality of the Maxwell principal reflection.**  If `C`
is a coframe, `E` its left inverse, and `C * S * E` is the canonical Maxwell
residual, then the coordinate stress action pulled into the principal frame
is exactly `q` times the canonical reflection. -/
theorem pull_mixedEndomorphismCovectorAction_eq_canonicalReflection
    (C E S : Matrix4) (q : ℝ) (v : OneForm4)
    (hEC : E * C = 1)
    (hcanonical : transportMixed C S E = canonicalMaxwellResidual q) :
    pullCovectorToPrincipalFrame E
        (mixedEndomorphismCovectorAction S v) =
      q • canonicalPrincipalReflectionCovector
        (pullCovectorToPrincipalFrame E v) := by
  have hSE : S * E = E * canonicalMaxwellResidual q := by
    calc
      S * E = (E * C) * (S * E) := by rw [hEC, one_mul]
      _ = E * (C * S * E) := by noncomm_ring
      _ = E * canonicalMaxwellResidual q := by
        simpa [transportMixed] using congrArg (fun X => E * X) hcanonical
  rw [mixedEndomorphismCovectorAction,
    pullCovectorToPrincipalFrame_comp, hSE,
    ← pullCovectorToPrincipalFrame_comp]
  simpa [mixedEndomorphismCovectorAction] using
    mixedEndomorphismCovectorAction_canonicalMaxwellResidual q
      (pullCovectorToPrincipalFrame E v)

/-- The same naturality identity with an arbitrary nonzero scalar
orientation factor.  For scalar reconstruction the intended values are
`epsilon = 1` and `epsilon = -1`. -/
theorem pull_mixedEndomorphismCovectorAction_smul_eq_canonicalReflection
    (C E S : Matrix4) (q epsilon : ℝ) (v : OneForm4)
    (hEC : E * C = 1)
    (hcanonical : transportMixed C S E = canonicalMaxwellResidual q) :
    pullCovectorToPrincipalFrame E
        (mixedEndomorphismCovectorAction S (epsilon • v)) =
      (epsilon * q) • canonicalPrincipalReflectionCovector
        (pullCovectorToPrincipalFrame E v) := by
  rw [mixedEndomorphismCovectorAction, pullCovectorToPrincipalFrame_smul,
    pullCovectorToPrincipalFrame_smul]
  have h := pull_mixedEndomorphismCovectorAction_eq_canonicalReflection
    C E S q v hEC hcanonical
  rw [mixedEndomorphismCovectorAction] at h
  rw [h]
  simp [smul_smul]

/-- Coordinate-free content of “two covectors have a nonzero wedge”: at
least one component is nonzero in the current coordinates. -/
def CovectorWedgeActive (omega v : OneForm4) : Prop :=
  ∃ i j : Fin 4, oneFormWedgeOneComponent omega v i j ≠ 0

/-- Pullback transports a one-form wedge by the expected two matrix
factors. -/
theorem oneFormWedgeOneComponent_pull
    (K : Matrix4) (omega v : OneForm4) (a b : Fin 4) :
    oneFormWedgeOneComponent
        (pullCovectorToPrincipalFrame K omega)
        (pullCovectorToPrincipalFrame K v) a b =
      ∑ i, ∑ j, K i a * K j b *
        oneFormWedgeOneComponent omega v i j := by
  simp [oneFormWedgeOneComponent, pullCovectorToPrincipalFrame,
    Fin.sum_univ_succ]
  ring

/-- A zero wedge remains zero after every covector pullback. -/
theorem covectorWedgeActive_pull_of_not
    (K : Matrix4) (omega v : OneForm4)
    (hzero : ¬ CovectorWedgeActive omega v) :
    ¬ CovectorWedgeActive
      (pullCovectorToPrincipalFrame K omega)
      (pullCovectorToPrincipalFrame K v) := by
  intro hactive
  obtain ⟨a, b, hab⟩ := hactive
  rw [oneFormWedgeOneComponent_pull] at hab
  apply hab
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hij : oneFormWedgeOneComponent omega v i j = 0 := by
    by_contra hne
    exact hzero ⟨i, j, hne⟩
  rw [hij, mul_zero]

/-- **Invertible-pullback invariance of the active wedge.**  Existence of a
nonzero wedge component is preserved by every covector pullback that has a
supplied inverse. -/
theorem covectorWedgeActive_pull_iff
    (K L : Matrix4) (omega v : OneForm4) (hKL : K * L = 1) :
    CovectorWedgeActive
        (pullCovectorToPrincipalFrame K omega)
        (pullCovectorToPrincipalFrame K v) ↔
      CovectorWedgeActive omega v := by
  constructor
  · contrapose!
    exact covectorWedgeActive_pull_of_not K omega v
  · intro hactive
    by_contra hpull
    have hback := covectorWedgeActive_pull_of_not L
      (pullCovectorToPrincipalFrame K omega)
      (pullCovectorToPrincipalFrame K v) hpull
    rw [pullCovectorToPrincipalFrame_comp,
      pullCovectorToPrincipalFrame_comp, hKL,
      pullCovectorToPrincipalFrame_one,
      pullCovectorToPrincipalFrame_one] at hback
    exact hback hactive

/-- Multiplying either member of a wedge by a nonzero scalar does not change
the active locus. -/
theorem covectorWedgeActive_smul_right_iff
    (omega v : OneForm4) (r : ℝ) (hr : r ≠ 0) :
    CovectorWedgeActive omega (r • v) ↔ CovectorWedgeActive omega v := by
  constructor
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    intro hzero
    have hscale :
        oneFormWedgeOneComponent omega (r • v) i j =
          r * oneFormWedgeOneComponent omega v i j := by
      simp only [oneFormWedgeOneComponent, Pi.smul_apply, smul_eq_mul]
      ring
    apply hij
    rw [hscale, hzero, mul_zero]
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    simp only [oneFormWedgeOneComponent, Pi.smul_apply, smul_eq_mul]
    have : omega i * (r * v j) - omega j * (r * v i) =
        r * oneFormWedgeOneComponent omega v i j := by
      unfold oneFormWedgeOneComponent
      ring
    rw [this]
    exact mul_ne_zero hr hij

/-- The active wedge is insensitive to the sign chosen for the scalar. -/
@[simp] theorem covectorWedgeActive_neg_right
    (omega v : OneForm4) :
    CovectorWedgeActive omega (-v) ↔ CovectorWedgeActive omega v := by
  simpa only [neg_one_smul] using
    covectorWedgeActive_smul_right_iff omega v (-1) (by norm_num)

/-- A choice-independent physical active predicate.  It is written entirely
in coordinate covectors and the physical mixed Maxwell stress; no principal
frame, scalar sign, or detector component is selected. -/
def IsCoordinateMaxwellStressActiveWedge
    (S : Matrix4) (omega v : OneForm4) : Prop :=
  CovectorWedgeActive omega (mixedEndomorphismCovectorAction S v)

/-- Scalar orientation does not affect the coordinate physical predicate. -/
@[simp] theorem isCoordinateMaxwellStressActiveWedge_neg_scalar
    (S : Matrix4) (omega v : OneForm4) :
    IsCoordinateMaxwellStressActiveWedge S omega (-v) ↔
      IsCoordinateMaxwellStressActiveWedge S omega v := by
  unfold IsCoordinateMaxwellStressActiveWedge
    mixedEndomorphismCovectorAction
  rw [show (-v : OneForm4) = (-1 : ℝ) • v by simp]
  rw [pullCovectorToPrincipalFrame_smul]
  simpa only [neg_one_smul] using
    covectorWedgeActive_smul_right_iff omega
      (pullCovectorToPrincipalFrame S v) (-1) (by norm_num)

/-- **Frame-independent physical/principal active-locus theorem.**  On a
non-null Maxwell branch, the coordinate stress predicate is equivalent to
the detector's principal-frame condition `omega ∧ Jv != 0`. -/
theorem isCoordinateMaxwellStressActiveWedge_iff_principal
    (C E S : Matrix4) (q : ℝ) (omega v : OneForm4)
    (hEC : E * C = 1) (hq : q ≠ 0)
    (hcanonical : transportMixed C S E = canonicalMaxwellResidual q) :
    IsCoordinateMaxwellStressActiveWedge S omega v ↔
      CovectorWedgeActive
        (pullCovectorToPrincipalFrame E omega)
        (canonicalPrincipalReflectionCovector
          (pullCovectorToPrincipalFrame E v)) := by
  unfold IsCoordinateMaxwellStressActiveWedge
  rw [← covectorWedgeActive_pull_iff E C omega
      (mixedEndomorphismCovectorAction S v) hEC]
  rw [pull_mixedEndomorphismCovectorAction_eq_canonicalReflection
    C E S q v hEC hcanonical]
  exact covectorWedgeActive_smul_right_iff
    (pullCovectorToPrincipalFrame E omega)
    (canonicalPrincipalReflectionCovector
      (pullCovectorToPrincipalFrame E v)) q hq

/-- Two different principal coframes canonicalizing the same physical
stress give the same active locus.  This is the direct frame-choice
confluence statement behind the coordinate predicate. -/
theorem principalCovectorWedgeActive_iff_of_commonCoordinateStress
    (C₁ E₁ C₂ E₂ S : Matrix4) (q : ℝ) (omega v : OneForm4)
    (hE₁C₁ : E₁ * C₁ = 1) (hE₂C₂ : E₂ * C₂ = 1)
    (hq : q ≠ 0)
    (hcanonical₁ : transportMixed C₁ S E₁ =
      canonicalMaxwellResidual q)
    (hcanonical₂ : transportMixed C₂ S E₂ =
      canonicalMaxwellResidual q) :
    CovectorWedgeActive
        (pullCovectorToPrincipalFrame E₁ omega)
        (canonicalPrincipalReflectionCovector
          (pullCovectorToPrincipalFrame E₁ v)) ↔
      CovectorWedgeActive
        (pullCovectorToPrincipalFrame E₂ omega)
        (canonicalPrincipalReflectionCovector
          (pullCovectorToPrincipalFrame E₂ v)) := by
  have h₁ := isCoordinateMaxwellStressActiveWedge_iff_principal
    C₁ E₁ S q omega v hE₁C₁ hq hcanonical₁
  have h₂ := isCoordinateMaxwellStressActiveWedge_iff_principal
    C₂ E₂ S q omega v hE₂C₂ hq hcanonical₂
  exact h₁.symm.trans h₂

/-- **Actual-metric specialization.**  Every upstream detector branch turns
the choice-independent coordinate stress predicate into exactly the selected
principal-frame active condition.  This theorem uses no channel acceptance
or matter-field realization. -/
theorem isCoordinateActualMetricMaxwellStressActiveWedge_iff_principal_of_upstream
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (omega v : OneForm4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice) :
    IsCoordinateMaxwellStressActiveWedge
        (actualMetricMaxwellResidualCandidateField4 g choice z) omega v ↔
      CovectorWedgeActive
        (pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹ omega)
        (canonicalPrincipalReflectionCovector
          (pullCovectorToPrincipalFrame
            (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹ v)) := by
  let C := actualMetricPrincipalCoframeCandidateField4 g choice z
  let E := C⁻¹
  let S := actualMetricMaxwellResidualCandidateField4 g choice z
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  apply isCoordinateMaxwellStressActiveWedge_iff_principal
    C E S q omega v
  · simpa [C, E] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice hupstream
  · exact ne_of_gt (by simpa [q] using
      IsActualMetricUpstreamEntranceAt4.qPos g z choice hupstream)
  · simpa [C, E, S, q] using
      actualMetricMaxwellResidual_transport_eq_canonical_of_upstream
        g z choice hupstream

/-- Extracting the effective one-form from an exact physical channel does
not alter the active locus: the hidden shear is parallel to `Jv` and drops
out of the wedge. -/
theorem covectorWedgeActive_extractedChannel_iff_physical
    (E : ℝ) (hE : E ≠ 0) (v omega : OneForm4) (A B : ℝ)
    (X : ThreeTensor4 × ThreeTensor4)
    (hX : X = canonicalComplexionCouplingChannels E v
      (effectiveComplexionOneForm omega
        (canonicalPrincipalReflectionCovector v) B) A) :
    CovectorWedgeActive
        (canonicalEffectiveOneFormFromChannels E X)
        (canonicalPrincipalReflectionCovector v) ↔
      CovectorWedgeActive omega
        (canonicalPrincipalReflectionCovector v) := by
  rw [canonicalEffectiveOneFormFromChannels_eq E hE v
    (effectiveComplexionOneForm omega
      (canonicalPrincipalReflectionCovector v) B) A X hX]
  constructor
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    simpa only [oneFormWedgeOneComponent_effectiveComplexionOneForm]
      using hij
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    simpa only [oneFormWedgeOneComponent_effectiveComplexionOneForm]
      using hij

/-- Explicit physical-channel relation needed only for the bridge to the
detector's curvature-extracted effective one-form.  It says that the raw
canonical seed channel is generated by a coordinate physical complexion
covector `omega`; the cosine and hidden sine amplitudes remain existential.
No acceptance predicate is included. -/
def IsActualMetricPhysicalEffectiveChannelAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (omega : OneForm4) : Prop :=
  let C := actualMetricPrincipalCoframeCandidateField4 g choice z
  let E := C⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus z
  ∃ A B : ℝ,
    curvatureSeedCanonicalChannelField
        (actualMetricPrincipalCoframeCandidateField4 g choice)
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z =
      canonicalComplexionCouplingChannels (Real.sqrt (2 * q))
        (pullCovectorToPrincipalFrame E v)
        (effectiveComplexionOneForm
          (pullCovectorToPrincipalFrame E omega)
          (canonicalPrincipalReflectionCovector
            (pullCovectorToPrincipalFrame E v)) B) A

/-- **A physical constant-coupling channel supplies a coordinate physical
complexion covector.**  This is a purely algebraic consequence of the
physical-channel normal form and upstream invertibility.  The hidden shear
is removed in the principal frame and the resulting covector is pushed back
to coordinates.  No detector acceptance is assumed. -/
theorem exists_actualMetricPhysicalEffectiveChannelAt4_of_upstream_physicalConstantCoupling
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
      g z choice a) :
    ∃ omega : OneForm4,
      IsActualMetricPhysicalEffectiveChannelAt4 g z choice omega := by
  let C := actualMetricPrincipalCoframeCandidateField4 g choice z
  let E := C⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus z
  let vP := pullCovectorToPrincipalFrame E v
  let X := curvatureSeedCanonicalChannelField
    (actualMetricPrincipalCoframeCandidateField4 g choice)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g)) z
  have hCE : C * E = 1 := by
    simpa [C, E] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice hupstream
  unfold IsActualMetricPhysicalConstantCouplingChannelAt at hphysical
  dsimp only at hphysical
  obtain ⟨eta, A, B, c, s, hX, hA, hB, hunit, hequation⟩ := hphysical
  let omegaP := eta - (B / 2) • canonicalPrincipalReflectionCovector vP
  let omegaCoord := pullCovectorToPrincipalFrame C omegaP
  have hpullOmega : pullCovectorToPrincipalFrame E omegaCoord = omegaP := by
    change pullCovectorToPrincipalFrame E
      (pullCovectorToPrincipalFrame C omegaP) = omegaP
    rw [pullCovectorToPrincipalFrame_comp, hCE,
      pullCovectorToPrincipalFrame_one]
  have heffective :
      effectiveComplexionOneForm omegaP
          (canonicalPrincipalReflectionCovector vP) B = eta := by
    funext i
    simp [omegaP, effectiveComplexionOneForm]
  refine ⟨omegaCoord, ?_⟩
  unfold IsActualMetricPhysicalEffectiveChannelAt4
  dsimp only
  refine ⟨A, B, ?_⟩
  change X = canonicalComplexionCouplingChannels (Real.sqrt (2 * q)) vP
    (effectiveComplexionOneForm
      (pullCovectorToPrincipalFrame E omegaCoord)
      (canonicalPrincipalReflectionCovector vP) B) A
  rw [hpullOmega, heffective]
  exact hX

/-- **Invariant bridge to the detector gate.**  On an upstream branch whose
raw channel has the explicit physical effective form, the detector's
principal-frame active predicate is exactly the coordinate, stress-only
predicate.  In particular, the generic locus is not an artifact of the
selected tetrad or finite wedge component, and this implication does not
assume detector acceptance. -/
theorem isActualMetricActiveFourthOrderWedgeAt_iff_coordinatePhysical
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (omega : OneForm4)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hchannel : IsActualMetricPhysicalEffectiveChannelAt4
      g z choice omega) :
    IsActualMetricActiveFourthOrderWedgeAt g z choice ↔
      IsCoordinateMaxwellStressActiveWedge
        (actualMetricMaxwellResidualCandidateField4 g choice z)
        omega
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z) := by
  let C := actualMetricPrincipalCoframeCandidateField4 g choice z
  let E := C⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus z
  let X := curvatureSeedCanonicalChannelField
    (actualMetricPrincipalCoframeCandidateField4 g choice)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g)) z
  obtain ⟨A, B, hX⟩ := hchannel
  have hq : 0 < q := by
    simpa [q] using
      IsActualMetricUpstreamEntranceAt4.qPos g z choice hupstream
  have hE : Real.sqrt (2 * q) ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (mul_pos (by norm_num) hq)
  have hprincipal := covectorWedgeActive_extractedChannel_iff_physical
    (Real.sqrt (2 * q)) hE
    (pullCovectorToPrincipalFrame E v)
    (pullCovectorToPrincipalFrame E omega) A B X hX
  have hinvariant :=
    isCoordinateActualMetricMaxwellStressActiveWedge_iff_principal_of_upstream
      g z choice omega v hupstream
  change CovectorWedgeActive
      (canonicalEffectiveOneFormFromChannels (Real.sqrt (2 * q)) X)
      (canonicalPrincipalReflectionCovector
        (pullCovectorToPrincipalFrame E v)) ↔
    IsCoordinateMaxwellStressActiveWedge
      (actualMetricMaxwellResidualCandidateField4 g choice z) omega v
  exact hprincipal.trans hinvariant.symm

/-- **Choice-free coordinate reformulation on physical data.**  Given
upstream entrance and a genuine constant-coupling channel, the detector's
active premise is equivalent to existence of a coordinate complexion
covector that both generates the physical effective channel and has nonzero
wedge with the stress-reflected scalar covector.  Neither side assumes
detector acceptance, and the right-hand active test contains no selected
principal frame or finite component index. -/
theorem isActualMetricActiveFourthOrderWedgeAt_iff_exists_coordinatePhysical
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
      g z choice a) :
    IsActualMetricActiveFourthOrderWedgeAt g z choice ↔
      ∃ omega : OneForm4,
        IsActualMetricPhysicalEffectiveChannelAt4 g z choice omega ∧
        IsCoordinateMaxwellStressActiveWedge
          (actualMetricMaxwellResidualCandidateField4 g choice z)
          omega
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) := by
  constructor
  · intro hactive
    obtain ⟨omega, heffective⟩ :=
      exists_actualMetricPhysicalEffectiveChannelAt4_of_upstream_physicalConstantCoupling
        g z choice a hupstream hphysical
    refine ⟨omega, heffective, ?_⟩
    exact (isActualMetricActiveFourthOrderWedgeAt_iff_coordinatePhysical
      g z choice omega hupstream heffective).mp hactive
  · rintro ⟨omega, heffective, hactive⟩
    exact (isActualMetricActiveFourthOrderWedgeAt_iff_coordinatePhysical
      g z choice omega hupstream heffective).mpr hactive

/-- Every coordinate covector realizing the same physical effective channel
gives the same answer to the stress-only active test.  This universal form
rules out dependence on which such physical complexion representative is
used. -/
theorem isActualMetricActiveFourthOrderWedgeAt_iff_forall_coordinatePhysical
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (a : ℝ)
    (hupstream : IsActualMetricUpstreamEntranceAt4 g z choice)
    (hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
      g z choice a) :
    IsActualMetricActiveFourthOrderWedgeAt g z choice ↔
      ∀ omega : OneForm4,
        IsActualMetricPhysicalEffectiveChannelAt4 g z choice omega →
        IsCoordinateMaxwellStressActiveWedge
          (actualMetricMaxwellResidualCandidateField4 g choice z)
          omega
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) := by
  constructor
  · intro hactive omega heffective
    exact (isActualMetricActiveFourthOrderWedgeAt_iff_coordinatePhysical
      g z choice omega hupstream heffective).mp hactive
  · intro hall
    obtain ⟨omega, heffective⟩ :=
      exists_actualMetricPhysicalEffectiveChannelAt4_of_upstream_physicalConstantCoupling
        g z choice a hupstream hphysical
    exact (isActualMetricActiveFourthOrderWedgeAt_iff_coordinatePhysical
      g z choice omega hupstream heffective).mpr (hall omega heffective)

/-!
The principal audit anchors for this module are:

* `pull_mixedEndomorphismCovectorAction_eq_canonicalReflection`;
* `covectorWedgeActive_pull_iff`;
* `isCoordinateMaxwellStressActiveWedge_iff_principal`;
* `principalCovectorWedgeActive_iff_of_commonCoordinateStress`;
* `isCoordinateActualMetricMaxwellStressActiveWedge_iff_principal_of_upstream`;
* `exists_actualMetricPhysicalEffectiveChannelAt4_of_upstream_physicalConstantCoupling`;
* `isActualMetricActiveFourthOrderWedgeAt_iff_coordinatePhysical`.
* `isActualMetricActiveFourthOrderWedgeAt_iff_exists_coordinatePhysical`;
* `isActualMetricActiveFourthOrderWedgeAt_iff_forall_coordinatePhysical`.
-/

end RainichKaluza
