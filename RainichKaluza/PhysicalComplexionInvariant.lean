import RainichKaluza.InvariantActiveWedge
import RainichKaluza.NorthStarComposition
import Mathlib.Tactic.NoncommRing

/-!
# Choice-free physical complexion covector

Maxwell stress does not determine electromagnetic complexion: pointwise
duality rotations leave the stress unchanged.  A genuine physical Maxwell
field and its metric Hodge partner do determine the *double-angle* scalars

`C = cos (2 theta)` and `S = sin (2 theta)`.

This module isolates the exact local invariant needed by the fourth-order
active-wedge gate.  The physical complexion covector is reconstructed without
choosing a half-angle by

`omega = (C dS - S dC) / 2`.

For any unit-circle lift `(c,s)` of `(C,S)`, this equals `c ds - s dc`.
Consequently it is unchanged by the unavoidable simultaneous sign change
`(c,s) -> (-c,-s)`.  The final definitions use scalar contractions of the
coordinate physical pair `(F,*F)` and the inverse metric, so no principal
coframe or detector component enters the physical active predicate.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix Filter

/-- **Source-free physical channel germ splice.**  This is the part of the
patchwise physical-channel theorem that precedes quotient differentiation.
It derives the complete canonical seed-channel normal form at `z` without
choosing a nonzero scalar component and without assuming detector
acceptance or active-wedge genericity. -/
theorem curvatureSeedCanonicalChannelField_eq_physical_of_patch_physicalSeedGerms
    {U : Set CurvatureCoordinateSpace4}
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (a : ℝ) (z : CurvatureCoordinateSpace4)
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
    curvatureSeedCanonicalChannelField L q z =
      canonicalPhysicalSeedChannels (Real.sqrt (2 * q z))
        (pullCovectorToPrincipalFrame (L z)⁻¹ (v z))
        (pullCovectorToPrincipalFrame (L z)⁻¹ (omega z))
        (a * (c z ^ 2 - s z ^ 2)) (a * (2 * c z * s z)) := by
  let M := PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
    L q omega c s a hdc hds
  let S : PositiveQPhaseIIISeedPairC1Realization M :=
    PositiveQPhaseIIISeedPairC1Realization.ofActualSmoothFields
      L q omega c s a hdc hds hopen hLSmooth hqSmooth hqPos
        hcSmooth hsSmooth
  have hzGerms := hgerms z hz
  have hFrealized : physicalF.field =ᶠ[nhds z] S.rotatedC1.field := by
    filter_upwards [hzGerms.1, hopen.mem_nhds hz] with x hx hxU
    calc
      physicalF.field x = (M.exteriorJet x).rotatedF := hx
      _ = S.rotatedC1.field x :=
        (S.toRescaledMaxwellC1Realization.field_eq x hxU).symm
  have hGrealized :
      physicalG.field =ᶠ[nhds z] S.rotatedHodgeC1.field := by
    filter_upwards [hzGerms.2, hopen.mem_nhds hz] with x hx hxU
    calc
      physicalG.field x = (M.exteriorJet x).rotatedG := hx
      _ = S.rotatedHodgeC1.field x :=
        (S.toRescaledMaxwellC1PairRealization.hodge_field_eq x hxU).symm
  have hseedClosure : EMDExteriorClosure matrixOneWedgeTwo (v z) a
      (M.exteriorJet z).rotatedF (M.exteriorJet z).rotatedG
      ((M.exteriorJet z).rotatedDF matrixOneWedgeTwo)
      ((M.exteriorJet z).rotatedDG matrixOneWedgeTwo) :=
    S.exteriorJet_emdExteriorClosure_of_physicalFields_eventuallyEq
      physicalF physicalG z hz (v z) a hFrealized hGrealized
        (hclosure z hz)
  unfold curvatureSeedCanonicalChannelField
  simpa [M, PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
    matrixFieldCoordinateFDeriv4] using
    transportedPositiveQCanonicalSeedChannels_eq_physical_of_emdClosure
      (L z) (L z)⁻¹ (matrixFieldCoordinateFDeriv4 L z)
      (q z) (scalarFieldCoordinateFDeriv q z) (v z) (omega z) a
      (c z) (s z) (scalarFieldCoordinateFDeriv c z)
      (scalarFieldCoordinateFDeriv s z) (hLK z hz) (hunit z hz)
      (hdc z hz) (hds z hz) hseedClosure

/-- Trace pairing of two covariant two-forms using a contravariant metric.
For `H = F` this is the matrix scalar already occurring in Maxwell stress. -/
noncomputable def coordinateTwoFormTracePairing
    (GInv F H : Matrix4) : ℝ :=
  Matrix.trace (GInv * F * GInv * H)

/-- Double-angle cosine reconstructed from a genuine physical Maxwell form.
The normalization is adapted to the positive non-null stress eigenvalue `q`. -/
noncomputable def physicalMaxwellDoubleAngleCosine
    (GInv F : Matrix4) (q : ℝ) : ℝ :=
  coordinateTwoFormTracePairing GInv F F / (4 * q)

/-- Double-angle sine reconstructed from a genuine Maxwell/Hodge pair.
The sign follows the canonical Hodge convention `*(E,B)=(-B,E)`. -/
noncomputable def physicalMaxwellDoubleAngleSine
    (GInv F H : Matrix4) (q : ℝ) : ℝ :=
  -coordinateTwoFormTracePairing GInv F H / (4 * q)

/-- Product-rule covector for `C = c²-s²`. -/
def doubleAngleCosineOneForm
    (c s : ℝ) (dc ds : OneForm4) : OneForm4 :=
  fun i => 2 * c * dc i - 2 * s * ds i

/-- Product-rule covector for `S = 2cs`. -/
def doubleAngleSineOneForm
    (c s : ℝ) (dc ds : OneForm4) : OneForm4 :=
  fun i => 2 * s * dc i + 2 * c * ds i

/-- Half-angle-free reconstruction of the physical complexion covector. -/
noncomputable def physicalComplexionOneFormFromDoubleAngle
    (C S : ℝ) (dC dS : OneForm4) : OneForm4 :=
  fun i => (C * dS i - S * dC i) / 2

/-- The ordinary unit-circle complexion covector, written componentwise. -/
def dualityComplexionOneForm
    (c s : ℝ) (dc ds : OneForm4) : OneForm4 :=
  fun i => complexionRate c s (dc i) (ds i)

/-- **Double-angle descent.**  The half-angle-free formula reconstructs the
same complexion covector from every unit-circle lift. -/
theorem physicalComplexionOneFormFromDoubleAngle_eq_dualityComplexion
    (c s : ℝ) (dc ds : OneForm4)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    physicalComplexionOneFormFromDoubleAngle
        (c ^ 2 - s ^ 2) (2 * c * s)
        (doubleAngleCosineOneForm c s dc ds)
        (doubleAngleSineOneForm c s dc ds) =
      dualityComplexionOneForm c s dc ds := by
  funext i
  simp only [physicalComplexionOneFormFromDoubleAngle,
    doubleAngleCosineOneForm, doubleAngleSineOneForm,
    dualityComplexionOneForm, complexionRate]
  calc
    ((c ^ 2 - s ^ 2) * (2 * s * dc i + 2 * c * ds i) -
          (2 * c * s) * (2 * c * dc i - 2 * s * ds i)) / 2 =
        (c ^ 2 + s ^ 2) * (c * ds i - s * dc i) := by ring
    _ = c * ds i - s * dc i := by rw [hunit, one_mul]

/-- The double-angle data are unchanged under the simultaneous sign change
of a unit-circle lift. -/
theorem physicalComplexionOneFormFromDoubleAngle_neg_lift
    (c s : ℝ) (dc ds : OneForm4) :
    physicalComplexionOneFormFromDoubleAngle
        ((-c) ^ 2 - (-s) ^ 2) (2 * (-c) * (-s))
        (doubleAngleCosineOneForm (-c) (-s) (-dc) (-ds))
        (doubleAngleSineOneForm (-c) (-s) (-dc) (-ds)) =
      physicalComplexionOneFormFromDoubleAngle
        (c ^ 2 - s ^ 2) (2 * c * s)
        (doubleAngleCosineOneForm c s dc ds)
        (doubleAngleSineOneForm c s dc ds) := by
  funext i
  simp [physicalComplexionOneFormFromDoubleAngle,
    doubleAngleCosineOneForm, doubleAngleSineOneForm]

/-- Coordinate derivative of the double-angle cosine field. -/
theorem scalarFieldCoordinateFDeriv_doubleAngleCosine_oneForm
    (c s : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z) :
    scalarFieldCoordinateFDeriv (fun y => c y ^ 2 - s y ^ 2) z =
      doubleAngleCosineOneForm (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) := by
  have h := scalarFieldCoordinateFDeriv_doubleAngleCosine 1 c s z hc hs
  simp only [one_mul] at h
  rw [h]
  funext i
  simp [doubleAngleCosineFirstDerivative,
    doubleAngleCosineOneForm]

/-- Coordinate derivative of the double-angle sine field. -/
theorem scalarFieldCoordinateFDeriv_doubleAngleSine_oneForm
    (c s : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z) :
    scalarFieldCoordinateFDeriv (fun y => 2 * c y * s y) z =
      doubleAngleSineOneForm (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) := by
  rw [show (fun y => 2 * c y * s y) =
      (fun y => 2 * (c * s) y) by
    funext y
    change 2 * c y * s y = 2 * (c y * s y)
    ring]
  funext k
  unfold scalarFieldCoordinateFDeriv doubleAngleSineOneForm
  rw [fderiv_const_mul (hc.mul hs) 2, fderiv_mul hc hs]
  simp
  ring

/-- The two invariant scalar fields associated with genuine physical data. -/
noncomputable def physicalMaxwellDoubleAngleCosineField
    (GInv F : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ) :
    CurvatureCoordinateSpace4 → ℝ :=
  fun z => physicalMaxwellDoubleAngleCosine (GInv z) (F z) (q z)

noncomputable def physicalMaxwellDoubleAngleSineField
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ) :
    CurvatureCoordinateSpace4 → ℝ :=
  fun z => physicalMaxwellDoubleAngleSine (GInv z) (F z) (H z) (q z)

/-- **Choice-free physical complexion covector.**  It is built directly
from the inverse metric, genuine physical Maxwell/Hodge fields, and `q`.
There is no selected principal coframe, half-angle, or detector channel. -/
noncomputable def coordinatePhysicalComplexionOneForm
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) : OneForm4 :=
  let C := physicalMaxwellDoubleAngleCosineField GInv F q
  let S := physicalMaxwellDoubleAngleSineField GInv F H q
  physicalComplexionOneFormFromDoubleAngle (C z) (S z)
    (scalarFieldCoordinateFDeriv C z)
    (scalarFieldCoordinateFDeriv S z)

/-- If the physical scalar contractions agree locally with a unit-circle
lift's double-angle functions, the coordinate construction is exactly the
ordinary complexion covector of that lift. -/
theorem coordinatePhysicalComplexionOneForm_eq_of_doubleAngle_germs
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (c s : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hC : physicalMaxwellDoubleAngleCosineField GInv F q =ᶠ[nhds z]
      (fun y => c y ^ 2 - s y ^ 2))
    (hS : physicalMaxwellDoubleAngleSineField GInv F H q =ᶠ[nhds z]
      (fun y => 2 * c y * s y))
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z)
    (hunit : c z ^ 2 + s z ^ 2 = 1) :
    coordinatePhysicalComplexionOneForm GInv F H q z =
      dualityComplexionOneForm (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) := by
  have hCz := hC.self_of_nhds
  have hSz := hS.self_of_nhds
  have hdC :
      scalarFieldCoordinateFDeriv
          (physicalMaxwellDoubleAngleCosineField GInv F q) z =
        scalarFieldCoordinateFDeriv (fun y => c y ^ 2 - s y ^ 2) z := by
    unfold scalarFieldCoordinateFDeriv
    rw [Filter.EventuallyEq.fderiv_eq hC]
  have hdS :
      scalarFieldCoordinateFDeriv
          (physicalMaxwellDoubleAngleSineField GInv F H q) z =
        scalarFieldCoordinateFDeriv (fun y => 2 * c y * s y) z := by
    unfold scalarFieldCoordinateFDeriv
    rw [Filter.EventuallyEq.fderiv_eq hS]
  unfold coordinatePhysicalComplexionOneForm
  dsimp only
  rw [hCz, hSz, hdC, hdS,
    scalarFieldCoordinateFDeriv_doubleAngleCosine_oneForm c s z hc hs,
    scalarFieldCoordinateFDeriv_doubleAngleSine_oneForm c s z hc hs]
  exact physicalComplexionOneFormFromDoubleAngle_eq_dualityComplexion
    (c z) (s z) _ _ hunit

/-- The trace pairing is invariant under a simultaneous arbitrary change of
basis of the contravariant metric and both covariant two-forms. -/
theorem coordinateTwoFormTracePairing_changeBasis
    (GInv L K F H : Matrix4)
    (hKL : K * L = 1) (_hLK : L * K = 1) :
    coordinateTwoFormTracePairing
        (L * GInv * Lᵀ) (transportTwoForm K F) (transportTwoForm K H) =
      coordinateTwoFormTracePairing GInv F H := by
  have htrans : Lᵀ * Kᵀ = (1 : Matrix4) := by
    rw [← Matrix.transpose_mul, hKL, Matrix.transpose_one]
  unfold coordinateTwoFormTracePairing transportTwoForm
  have hcore :
      (L * GInv * Lᵀ) * (Kᵀ * F * K) *
          (L * GInv * Lᵀ) * (Kᵀ * H * K) =
        L * (GInv * F * GInv * H) * K := by
    rw [show
      (L * GInv * Lᵀ) * (Kᵀ * F * K) *
          (L * GInv * Lᵀ) * (Kᵀ * H * K) =
        L * GInv * (Lᵀ * Kᵀ) * F * (K * L) * GInv *
          (Lᵀ * Kᵀ) * H * K by noncomm_ring]
    rw [htrans, hKL]
    simp
    noncomm_ring
  rw [hcore]
  calc
    Matrix.trace (L * (GInv * F * GInv * H) * K) =
        Matrix.trace (K * (L * (GInv * F * GInv * H))) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((K * L) * (GInv * F * GInv * H)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (GInv * F * GInv * H) := by rw [hKL, one_mul]

/-- The double-angle cosine is independent of which invertible frame is used
to evaluate the physical scalar. -/
theorem physicalMaxwellDoubleAngleCosine_changeBasis
    (GInv L K F : Matrix4) (q : ℝ)
    (hKL : K * L = 1) (hLK : L * K = 1) :
    physicalMaxwellDoubleAngleCosine
        (L * GInv * Lᵀ) (transportTwoForm K F) q =
      physicalMaxwellDoubleAngleCosine GInv F q := by
  unfold physicalMaxwellDoubleAngleCosine
  rw [coordinateTwoFormTracePairing_changeBasis GInv L K F F hKL hLK]

/-- The double-angle sine is likewise frame independent. -/
theorem physicalMaxwellDoubleAngleSine_changeBasis
    (GInv L K F H : Matrix4) (q : ℝ)
    (hKL : K * L = 1) (hLK : L * K = 1) :
    physicalMaxwellDoubleAngleSine
        (L * GInv * Lᵀ) (transportTwoForm K F) (transportTwoForm K H) q =
      physicalMaxwellDoubleAngleSine GInv F H q := by
  unfold physicalMaxwellDoubleAngleSine
  rw [coordinateTwoFormTracePairing_changeBasis GInv L K F H hKL hLK]

/-- Canonical evaluation of the physical double-angle cosine. -/
theorem physicalMaxwellDoubleAngleCosine_canonical
    (E c s : ℝ) (hE : E ≠ 0) :
    physicalMaxwellDoubleAngleCosine minkowskiMetric
        (c • canonicalMaxwellTwoForm E 0 +
          s • canonicalHodgeStar E 0) (E ^ 2 / 2) =
      c ^ 2 - s ^ 2 := by
  unfold physicalMaxwellDoubleAngleCosine coordinateTwoFormTracePairing
  simp [minkowskiMetric, canonicalMaxwellTwoForm, canonicalHodgeStar,
    Matrix.trace, Fin.sum_univ_succ]
  field_simp [hE]
  ring

/-- Canonical evaluation of the physical double-angle sine. -/
theorem physicalMaxwellDoubleAngleSine_canonical
    (E c s : ℝ) (hE : E ≠ 0) :
    physicalMaxwellDoubleAngleSine minkowskiMetric
        (c • canonicalMaxwellTwoForm E 0 +
          s • canonicalHodgeStar E 0)
        ((-s) • canonicalMaxwellTwoForm E 0 +
          c • canonicalHodgeStar E 0) (E ^ 2 / 2) =
      2 * c * s := by
  unfold physicalMaxwellDoubleAngleSine coordinateTwoFormTracePairing
  simp [minkowskiMetric, canonicalMaxwellTwoForm, canonicalHodgeStar,
    Matrix.trace, Fin.sum_univ_succ]
  field_simp [hE]
  ring

/-- **Adapted-frame evaluation.**  If any invertible coframe carries the
physical inverse metric and Maxwell/Hodge pair to a canonical duality
rotation, then the coordinate contractions recover its double-angle data.
The result does not depend on that coframe. -/
theorem physicalMaxwellDoubleAngles_of_adapted_duality
    (GInv L K F H : Matrix4) (q E c s : ℝ)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hmetric : L * GInv * Lᵀ = minkowskiMetric)
    (hpullF : transportTwoForm K F =
      c • canonicalMaxwellTwoForm E 0 +
        s • canonicalHodgeStar E 0)
    (hpullH : transportTwoForm K H =
      (-s) • canonicalMaxwellTwoForm E 0 +
        c • canonicalHodgeStar E 0)
    (hq : q = E ^ 2 / 2) (hE : E ≠ 0) :
    physicalMaxwellDoubleAngleCosine GInv F q = c ^ 2 - s ^ 2 ∧
      physicalMaxwellDoubleAngleSine GInv F H q = 2 * c * s := by
  constructor
  · calc
      physicalMaxwellDoubleAngleCosine GInv F q =
          physicalMaxwellDoubleAngleCosine
            (L * GInv * Lᵀ) (transportTwoForm K F) q :=
        (physicalMaxwellDoubleAngleCosine_changeBasis
          GInv L K F q hKL hLK).symm
      _ = physicalMaxwellDoubleAngleCosine minkowskiMetric
          (c • canonicalMaxwellTwoForm E 0 +
            s • canonicalHodgeStar E 0) (E ^ 2 / 2) := by
        rw [hmetric, hpullF, hq]
      _ = c ^ 2 - s ^ 2 :=
        physicalMaxwellDoubleAngleCosine_canonical E c s hE
  · calc
      physicalMaxwellDoubleAngleSine GInv F H q =
          physicalMaxwellDoubleAngleSine
            (L * GInv * Lᵀ) (transportTwoForm K F)
              (transportTwoForm K H) q :=
        (physicalMaxwellDoubleAngleSine_changeBasis
          GInv L K F H q hKL hLK).symm
      _ = physicalMaxwellDoubleAngleSine minkowskiMetric
          (c • canonicalMaxwellTwoForm E 0 +
            s • canonicalHodgeStar E 0)
          ((-s) • canonicalMaxwellTwoForm E 0 +
            c • canonicalHodgeStar E 0) (E ^ 2 / 2) := by
        rw [hmetric, hpullF, hpullH, hq]
      _ = 2 * c * s :=
        physicalMaxwellDoubleAngleSine_canonical E c s hE

/-- Physical sign reversal `(F,H) -> (-F,-H)` leaves the double-angle
scalars unchanged. -/
theorem physicalMaxwellDoubleAngles_neg
    (GInv F H : Matrix4) (q : ℝ) :
    physicalMaxwellDoubleAngleCosine GInv (-F) q =
        physicalMaxwellDoubleAngleCosine GInv F q ∧
      physicalMaxwellDoubleAngleSine GInv (-F) (-H) q =
        physicalMaxwellDoubleAngleSine GInv F H q := by
  constructor
  · unfold physicalMaxwellDoubleAngleCosine coordinateTwoFormTracePairing
    congr 1
    congr 1
    noncomm_ring
  · unfold physicalMaxwellDoubleAngleSine coordinateTwoFormTracePairing
    congr 1
    congr 2
    noncomm_ring

/-- Simultaneously reversing the genuine physical Maxwell/Hodge pair leaves
the coordinate physical complexion covector unchanged, including its actual
coordinate derivative. -/
theorem coordinatePhysicalComplexionOneForm_neg_physicalPair
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) :
    coordinatePhysicalComplexionOneForm GInv
        (fun y => -(F y)) (fun y => -(H y)) q z =
      coordinatePhysicalComplexionOneForm GInv F H q z := by
  have hC :
      physicalMaxwellDoubleAngleCosineField GInv (fun y => -(F y)) q =
        physicalMaxwellDoubleAngleCosineField GInv F q := by
    funext y
    exact (physicalMaxwellDoubleAngles_neg
      (GInv y) (F y) (H y) (q y)).1
  have hS :
      physicalMaxwellDoubleAngleSineField GInv
          (fun y => -(F y)) (fun y => -(H y)) q =
        physicalMaxwellDoubleAngleSineField GInv F H q := by
    funext y
    exact (physicalMaxwellDoubleAngles_neg
      (GInv y) (F y) (H y) (q y)).2
  unfold coordinatePhysicalComplexionOneForm
  rw [hC, hS]

/-- **Varying-frame choice independence.**  Even when the adapted frame
varies with position, evaluating the physical scalars in that frame gives
the same scalar fields and hence the same physical complexion derivative.
No derivatives of the frame are required for this equality. -/
theorem coordinatePhysicalComplexionOneForm_changeBasis
    (GInv L K F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hKL : ∀ y, K y * L y = 1)
    (hLK : ∀ y, L y * K y = 1) :
    coordinatePhysicalComplexionOneForm
        (fun y => L y * GInv y * (L y)ᵀ)
        (fun y => transportTwoForm (K y) (F y))
        (fun y => transportTwoForm (K y) (H y)) q z =
      coordinatePhysicalComplexionOneForm GInv F H q z := by
  have hC :
      physicalMaxwellDoubleAngleCosineField
          (fun y => L y * GInv y * (L y)ᵀ)
          (fun y => transportTwoForm (K y) (F y)) q =
        physicalMaxwellDoubleAngleCosineField GInv F q := by
    funext y
    exact physicalMaxwellDoubleAngleCosine_changeBasis
      (GInv y) (L y) (K y) (F y) (q y) (hKL y) (hLK y)
  have hS :
      physicalMaxwellDoubleAngleSineField
          (fun y => L y * GInv y * (L y)ᵀ)
          (fun y => transportTwoForm (K y) (F y))
          (fun y => transportTwoForm (K y) (H y)) q =
        physicalMaxwellDoubleAngleSineField GInv F H q := by
    funext y
    exact physicalMaxwellDoubleAngleSine_changeBasis
      (GInv y) (L y) (K y) (F y) (H y) (q y) (hKL y) (hLK y)
  unfold coordinatePhysicalComplexionOneForm
  rw [hC, hS]

/-- Patchwise adapted duality coordinates identify the choice-free physical
complexion covector with the stress-fibre complexion covector at every point
of differentiability.  This is the direct splice used by the North Star
physical-field realization. -/
theorem coordinatePhysicalComplexionOneForm_eq_of_adapted_duality_patch
    {U : Set CurvatureCoordinateSpace4}
    (GInv L K F H : CurvatureCoordinateSpace4 → Matrix4)
    (q E c s : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hKL : ∀ y ∈ U, K y * L y = 1)
    (hLK : ∀ y ∈ U, L y * K y = 1)
    (hmetric : ∀ y ∈ U,
      L y * GInv y * (L y)ᵀ = minkowskiMetric)
    (hpullF : ∀ y ∈ U, transportTwoForm (K y) (F y) =
      c y • canonicalMaxwellTwoForm (E y) 0 +
        s y • canonicalHodgeStar (E y) 0)
    (hpullH : ∀ y ∈ U, transportTwoForm (K y) (H y) =
      (-s y) • canonicalMaxwellTwoForm (E y) 0 +
        c y • canonicalHodgeStar (E y) 0)
    (hq : ∀ y ∈ U, q y = E y ^ 2 / 2)
    (hE : ∀ y ∈ U, E y ≠ 0)
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z)
    (hunit : c z ^ 2 + s z ^ 2 = 1) :
    coordinatePhysicalComplexionOneForm GInv F H q z =
      dualityComplexionOneForm (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) := by
  have hC : physicalMaxwellDoubleAngleCosineField GInv F q =ᶠ[nhds z]
      (fun y => c y ^ 2 - s y ^ 2) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact (physicalMaxwellDoubleAngles_of_adapted_duality
      (GInv y) (L y) (K y) (F y) (H y)
      (q y) (E y) (c y) (s y)
      (hKL y hy) (hLK y hy) (hmetric y hy)
      (hpullF y hy) (hpullH y hy) (hq y hy) (hE y hy)).1
  have hS : physicalMaxwellDoubleAngleSineField GInv F H q =ᶠ[nhds z]
      (fun y => 2 * c y * s y) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact (physicalMaxwellDoubleAngles_of_adapted_duality
      (GInv y) (L y) (K y) (F y) (H y)
      (q y) (E y) (c y) (s y)
      (hKL y hy) (hLK y hy) (hmetric y hy)
      (hpullF y hy) (hpullH y hy) (hq y hy) (hE y hy)).2
  exact coordinatePhysicalComplexionOneForm_eq_of_doubleAngle_germs
    GInv F H q c s z hC hS hc hs hunit

/-- Positive-`q` specialization with the canonical amplitude
`E = sqrt (2q)`. -/
theorem coordinatePhysicalComplexionOneForm_eq_of_positiveQ_adapted_duality_patch
    {U : Set CurvatureCoordinateSpace4}
    (GInv L K F H : CurvatureCoordinateSpace4 → Matrix4)
    (q c s : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hKL : ∀ y ∈ U, K y * L y = 1)
    (hLK : ∀ y ∈ U, L y * K y = 1)
    (hmetric : ∀ y ∈ U,
      L y * GInv y * (L y)ᵀ = minkowskiMetric)
    (hpullF : ∀ y ∈ U, transportTwoForm (K y) (F y) =
      c y • canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
        s y • canonicalHodgeStar (Real.sqrt (2 * q y)) 0)
    (hpullH : ∀ y ∈ U, transportTwoForm (K y) (H y) =
      (-s y) • canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
        c y • canonicalHodgeStar (Real.sqrt (2 * q y)) 0)
    (hqPos : ∀ y ∈ U, 0 < q y)
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z)
    (hunit : c z ^ 2 + s z ^ 2 = 1) :
    coordinatePhysicalComplexionOneForm GInv F H q z =
      dualityComplexionOneForm (c z) (s z)
        (scalarFieldCoordinateFDeriv c z)
        (scalarFieldCoordinateFDeriv s z) := by
  apply coordinatePhysicalComplexionOneForm_eq_of_adapted_duality_patch
    GInv L K F H q (fun y => Real.sqrt (2 * q y)) c s z
    hopen hz hKL hLK hmetric hpullF hpullH
  · intro y hy
    have hnonneg : 0 ≤ 2 * q y := (mul_pos (by norm_num) (hqPos y hy)).le
    rw [Real.sq_sqrt hnonneg]
    ring
  · intro y hy
    exact Real.sqrt_ne_zero'.mpr (mul_pos (by norm_num) (hqPos y hy))
  · exact hc
  · exact hs
  · exact hunit

/-- **Choice-free physical effective-channel entrance.**  On one fixed
actual-metric upstream branch, genuine `C¹` Maxwell/Hodge fields with the
reconstructed stress, physical Hodge relation, and EMD exterior closure force
the complete detector seed channel to have the physical effective normal
form generated by `coordinatePhysicalComplexionOneForm`.

This result is deliberately upstream of quotient source selection and of the
active-wedge gate: neither a nonzero source component nor any fourth-order
wedge component occurs among its hypotheses. -/
theorem isActualMetricPhysicalEffectiveChannelAt4_of_patch_physicalHodgeFields
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
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y))) :
    IsActualMetricPhysicalEffectiveChannelAt4 g z choice
      (coordinatePhysicalComplexionOneForm
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
        physicalF.field physicalG.field
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z) := by
  classical
  let GInv := fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹
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
  let omega := coordinatePhysicalComplexionOneForm
    GInv physicalF.field physicalG.field q
  have hLSmoothOne : MatrixFieldContDiffOn 1 U L := by
    intro i j
    exact (hLSmooth i j).of_le (by norm_num)
  have hKSmooth : MatrixFieldContDiffOn 1 U K := by
    simpa [L, K] using
      matrixFieldContDiffOn_actualMetricPrincipalCoframeCandidate_inv_of_upstream
        g choice hLSmoothOne hupstream
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
  have hmetric : ∀ y ∈ U,
      L y * GInv y * (L y)ᵀ = minkowskiMetric := by
    intro y hy
    simpa [GInv, L] using
      actualMetricPrincipalCoframeCandidate_inverseMetric_of_upstream
        g y choice (hupstream y hy)
  have hstressFiber :
      ContDiffOn ℝ 1 c U ∧ ContDiffOn ℝ 1 s U ∧
        (∀ y ∈ U, c y ^ 2 + s y ^ 2 = 1) ∧
        ∀ y ∈ U,
          pulledF y = c y •
                canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
              s y • canonicalHodgeStar (Real.sqrt (2 * q y)) 0 := by
    simpa [L, q, K, pulledF, c, s] using
      smoothActualMetricAdaptedMaxwellStressFiber_coordinates_of_c1
        g choice physicalF hopen (hqSmooth.of_le (by norm_num))
          hKSmooth hupstream hstress
  have hpullH : ∀ y ∈ U,
      transportTwoForm (K y) (physicalG.field y) =
        (-s y) • canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
          c y • canonicalHodgeStar (Real.sqrt (2 * q y)) 0 := by
    intro y hy
    let H0 := (-s y) • canonicalMaxwellTwoForm
        (Real.sqrt (2 * q y)) 0 +
      c y • canonicalHodgeStar (Real.sqrt (2 * q y)) 0
    have hfields :=
      physicalFields_eq_localPositiveQExteriorDualityJet_of_pullback_hodge
        (coordinateMetricMatrixField4 g y) (L y) (K y)
        (physicalF.field y) (physicalG.field y) (q y) (c y) (s y)
        (fun k i j ↦ scalarFieldCoordinateFDeriv (fun w ↦ L w i j) y k)
        (scalarFieldCoordinateFDeriv q y)
        (scalarFieldCoordinateFDeriv c y)
        (scalarFieldCoordinateFDeriv s y)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_metric_of_upstream
            g y choice (hupstream y hy)).symm)
        (hKL y hy) (hLK y hy)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
            g y choice (hupstream y hy)))
        (hstressFiber.2.2.2 y hy)
        (by simpa [L] using hphysicalHodge y hy)
    have hG := hfields.2
    change physicalG.field y =
      (-s y) • transportTwoForm (L y)
          (canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0) +
        c y • transportTwoForm (L y)
          (canonicalHodgeStar (Real.sqrt (2 * q y)) 0) at hG
    rw [← transportTwoForm_smul, ← transportTwoForm_smul,
      ← transportTwoForm_add_detector] at hG
    change physicalG.field y = transportTwoForm (L y) H0 at hG
    rw [hG, ← transportTwoForm_mul, hLK y hy]
    simp [H0, transportTwoForm]
  have homega : ∀ y ∈ U,
      omega y = dualityComplexionOneForm (c y) (s y)
        (scalarFieldCoordinateFDeriv c y)
        (scalarFieldCoordinateFDeriv s y) := by
    intro y hy
    exact coordinatePhysicalComplexionOneForm_eq_of_positiveQ_adapted_duality_patch
      GInv L K physicalF.field physicalG.field q c s y
      hopen hy hKL hLK hmetric hstressFiber.2.2.2 hpullH hqPos
      ((hstressFiber.1.differentiableOn_one y hy).differentiableAt
        (hopen.mem_nhds hy))
      ((hstressFiber.2.1.differentiableOn_one y hy).differentiableAt
        (hopen.mem_nhds hy))
      (hstressFiber.2.2.1 y hy)
  have hdc : ∀ y ∈ U,
      scalarFieldCoordinateFDeriv c y = (-s y) • omega y := by
    intro y hy
    have hcDiff :=
      (hstressFiber.1.differentiableOn_one y hy).differentiableAt
        (hopen.mem_nhds hy)
    have hsDiff :=
      (hstressFiber.2.1.differentiableOn_one y hy).differentiableAt
        (hopen.mem_nhds hy)
    have hunitLocal :
        (fun x => c x ^ 2 + s x ^ 2) =ᶠ[nhds y] (fun _ => (1 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hy] with x hx
      exact hstressFiber.2.2.1 x hx
    have htangent := scalarFieldCoordinateFDeriv_unitCircle_tangent
      c s y hcDiff hsDiff hunitLocal
    rw [homega y hy]
    funext i
    simpa [dualityComplexionOneForm, mul_comm] using
      (dualityParameter_derivative_eq_complexionRate
        (c y) (s y)
        (scalarFieldCoordinateFDeriv c y i)
        (scalarFieldCoordinateFDeriv s y i)
        (hstressFiber.2.2.1 y hy) (htangent i)).1
  have hds : ∀ y ∈ U,
      scalarFieldCoordinateFDeriv s y = c y • omega y := by
    intro y hy
    have hcDiff :=
      (hstressFiber.1.differentiableOn_one y hy).differentiableAt
        (hopen.mem_nhds hy)
    have hsDiff :=
      (hstressFiber.2.1.differentiableOn_one y hy).differentiableAt
        (hopen.mem_nhds hy)
    have hunitLocal :
        (fun x => c x ^ 2 + s x ^ 2) =ᶠ[nhds y] (fun _ => (1 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hy] with x hx
      exact hstressFiber.2.2.1 x hx
    have htangent := scalarFieldCoordinateFDeriv_unitCircle_tangent
      c s y hcDiff hsDiff hunitLocal
    rw [homega y hy]
    funext i
    simpa [dualityComplexionOneForm, mul_comm] using
      (dualityParameter_derivative_eq_complexionRate
        (c y) (s y)
        (scalarFieldCoordinateFDeriv c y i)
        (scalarFieldCoordinateFDeriv s y i)
        (hstressFiber.2.2.1 y hy) (htangent i)).2
  let M := PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
    L q omega c s a hdc hds
  have hgerms : ∀ y ∈ U,
      physicalF.field =ᶠ[nhds y]
          (fun x ↦ (M.exteriorJet x).rotatedF) ∧
        physicalG.field =ᶠ[nhds y]
          (fun x ↦ (M.exteriorJet x).rotatedG) := by
    intro y hy
    constructor <;> filter_upwards [hopen.mem_nhds hy] with x hx
    · exact (physicalFields_eq_localPositiveQExteriorDualityJet_of_pullback_hodge
        (coordinateMetricMatrixField4 g x) (L x) (K x)
        (physicalF.field x) (physicalG.field x) (q x) (c x) (s x)
        (fun k i j ↦ scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
        (scalarFieldCoordinateFDeriv q x)
        (scalarFieldCoordinateFDeriv c x)
        (scalarFieldCoordinateFDeriv s x)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_metric_of_upstream
            g x choice (hupstream x hx)).symm)
        (hKL x hx) (hLK x hx)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
            g x choice (hupstream x hx)))
        (hstressFiber.2.2.2 x hx)
        (by simpa [L] using hphysicalHodge x hx)).1
    · exact (physicalFields_eq_localPositiveQExteriorDualityJet_of_pullback_hodge
        (coordinateMetricMatrixField4 g x) (L x) (K x)
        (physicalF.field x) (physicalG.field x) (q x) (c x) (s x)
        (fun k i j ↦ scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
        (scalarFieldCoordinateFDeriv q x)
        (scalarFieldCoordinateFDeriv c x)
        (scalarFieldCoordinateFDeriv s x)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_metric_of_upstream
            g x choice (hupstream x hx)).symm)
        (hKL x hx) (hLK x hx)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
            g x choice (hupstream x hx)))
        (hstressFiber.2.2.2 x hx)
        (by simpa [L] using hphysicalHodge x hx)).2
  have hchannels :=
    curvatureSeedCanonicalChannelField_eq_physical_of_patch_physicalSeedGerms
      L q v omega c s physicalF physicalG a z hopen hz hLSmooth hqSmooth
      hqPos hstressFiber.1 hstressFiber.2.1 hstressFiber.2.2.1
      hdc hds (by simpa [L, K] using hLK)
      (by simpa [M] using hgerms) (by simpa [v] using hclosure)
  unfold IsActualMetricPhysicalEffectiveChannelAt4
  dsimp only
  refine ⟨a * (c z ^ 2 - s z ^ 2), a * (2 * c z * s z), ?_⟩
  have hfull := hchannels.trans
    (canonicalPhysicalSeedChannels_eq_full
      (Real.sqrt (2 * q z))
      (pullCovectorToPrincipalFrame (L z)⁻¹ (v z))
      (pullCovectorToPrincipalFrame (L z)⁻¹ (omega z))
      (a * (c z ^ 2 - s z ^ 2)) (a * (2 * c z * s z)))
  simpa [canonicalFullComplexionCouplingChannels,
    GInv, L, q, v, omega] using hfull

/-- Choice-free physical genericity predicate obtained by inserting the
physical double-angle complexion into the invariant stress-wedge test. -/
def IsPhysicalMaxwellComplexionActiveWedgeAt
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  IsCoordinateMaxwellStressActiveWedge (S z)
    (coordinatePhysicalComplexionOneForm GInv F H q z) (v z)

/-- On every local unit-circle realization, physical genericity is exactly
the active wedge formed with its ordinary complexion covector. -/
theorem isPhysicalMaxwellComplexionActiveWedgeAt_iff_of_doubleAngle_germs
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hC : physicalMaxwellDoubleAngleCosineField GInv F q =ᶠ[nhds z]
      (fun y => c y ^ 2 - s y ^ 2))
    (hS : physicalMaxwellDoubleAngleSineField GInv F H q =ᶠ[nhds z]
      (fun y => 2 * c y * s y))
    (hc : DifferentiableAt ℝ c z) (hs : DifferentiableAt ℝ s z)
    (hunit : c z ^ 2 + s z ^ 2 = 1) :
    IsPhysicalMaxwellComplexionActiveWedgeAt GInv F H q S v z ↔
      IsCoordinateMaxwellStressActiveWedge (S z)
        (dualityComplexionOneForm (c z) (s z)
          (scalarFieldCoordinateFDeriv c z)
          (scalarFieldCoordinateFDeriv s z)) (v z) := by
  unfold IsPhysicalMaxwellComplexionActiveWedgeAt
  rw [coordinatePhysicalComplexionOneForm_eq_of_doubleAngle_germs
    GInv F H q c s z hC hS hc hs hunit]

/-- The physical active predicate is insensitive to the unavoidable
simultaneous sign reversal of the genuine Maxwell/Hodge pair. -/
@[simp] theorem isPhysicalMaxwellComplexionActiveWedgeAt_neg_physicalPair
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) :
    IsPhysicalMaxwellComplexionActiveWedgeAt GInv
        (fun y => -(F y)) (fun y => -(H y)) q S v z ↔
      IsPhysicalMaxwellComplexionActiveWedgeAt GInv F H q S v z := by
  unfold IsPhysicalMaxwellComplexionActiveWedgeAt
  rw [coordinatePhysicalComplexionOneForm_neg_physicalPair]

/-- The physical active predicate is also insensitive to scalar orientation. -/
@[simp] theorem isPhysicalMaxwellComplexionActiveWedgeAt_neg_scalar
    (GInv F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) :
    IsPhysicalMaxwellComplexionActiveWedgeAt GInv F H q S
        (fun y => -(v y)) z ↔
      IsPhysicalMaxwellComplexionActiveWedgeAt GInv F H q S v z := by
  unfold IsPhysicalMaxwellComplexionActiveWedgeAt
  exact isCoordinateMaxwellStressActiveWedge_neg_scalar
    (S z) (coordinatePhysicalComplexionOneForm GInv F H q z) (v z)

/-- Evaluating the genuine pair in any varying invertible frame cannot change
the physical active-locus decision. -/
theorem isPhysicalMaxwellComplexionActiveWedgeAt_changeBasis
    (GInv L K F H : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4)
    (hKL : ∀ y, K y * L y = 1)
    (hLK : ∀ y, L y * K y = 1) :
    IsPhysicalMaxwellComplexionActiveWedgeAt
        (fun y => L y * GInv y * (L y)ᵀ)
        (fun y => transportTwoForm (K y) (F y))
        (fun y => transportTwoForm (K y) (H y)) q S v z ↔
      IsPhysicalMaxwellComplexionActiveWedgeAt GInv F H q S v z := by
  unfold IsPhysicalMaxwellComplexionActiveWedgeAt
  rw [coordinatePhysicalComplexionOneForm_changeBasis
    GInv L K F H q z hKL hLK]

/-- **Physical active locus equals the detector active gate.**  Under the
source-free physical effective-channel entrance proved above, the detector's
genericity condition is exactly the coordinate physical Maxwell-complexion
predicate.  This equivalence is established before any quotient source or
finite wedge component is selected. -/
theorem isActualMetricActiveFourthOrderWedgeAt_iff_physicalMaxwellComplexion
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
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y))) :
    IsActualMetricActiveFourthOrderWedgeAt g z choice ↔
      IsPhysicalMaxwellComplexionActiveWedgeAt
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
        physicalF.field physicalG.field
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g))
        (actualMetricMaxwellResidualCandidateField4 g choice)
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus) z := by
  let omega := coordinatePhysicalComplexionOneForm
    (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
    physicalF.field physicalG.field
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g))
  have hchannel : IsActualMetricPhysicalEffectiveChannelAt4
      g z choice (omega z) := by
    simpa [omega] using
      isActualMetricPhysicalEffectiveChannelAt4_of_patch_physicalHodgeFields
        g choice physicalF physicalG a z hopen hz hLSmooth hqSmooth
          hupstream hstress hphysicalHodge hclosure
  have H := isActualMetricActiveFourthOrderWedgeAt_iff_coordinatePhysical
    g z choice (omega z) (hupstream z hz) hchannel
  simpa [IsPhysicalMaxwellComplexionActiveWedgeAt, omega] using H

/-- Scalar-orbit form of the physical active-locus equivalence.  A selected
detector scalar may equal either orientation of an independently supplied
physical scalar covector; the active decision is the same in both cases. -/
theorem isActualMetricActiveFourthOrderWedgeAt_iff_physicalScalarOrbit
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (physicalV : CurvatureCoordinateSpace4 → OneForm4)
    (a : ℝ) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hLSmooth : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hqSmooth : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y)))
    (hscalar :
      actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z = physicalV z ∨
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z = -physicalV z) :
    IsActualMetricActiveFourthOrderWedgeAt g z choice ↔
      IsPhysicalMaxwellComplexionActiveWedgeAt
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
        physicalF.field physicalG.field
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g))
        (actualMetricMaxwellResidualCandidateField4 g choice)
        physicalV z := by
  rw [isActualMetricActiveFourthOrderWedgeAt_iff_physicalMaxwellComplexion
    g choice physicalF physicalG a z hopen hz hLSmooth hqSmooth
      hupstream hstress hphysicalHodge hclosure]
  unfold IsPhysicalMaxwellComplexionActiveWedgeAt
  rcases hscalar with hplus | hminus
  · rw [hplus]
  · rw [hminus]
    exact isCoordinateMaxwellStressActiveWedge_neg_scalar
      (actualMetricMaxwellResidualCandidateField4 g choice z)
      (coordinatePhysicalComplexionOneForm
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
        physicalF.field physicalG.field
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z)
      (physicalV z)

/-- The same active-locus equivalence with the stress argument written as
the genuine physical Maxwell stress.  The right-hand predicate now contains
no detector principal frame, residual, source, or wedge-component choice. -/
theorem isActualMetricActiveFourthOrderWedgeAt_iff_choiceFreePhysicalComplexion
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
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y))) :
    IsActualMetricActiveFourthOrderWedgeAt g z choice ↔
      IsPhysicalMaxwellComplexionActiveWedgeAt
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
        physicalF.field physicalG.field
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g))
        (fun y ↦ matrixMaxwellStress
          (coordinateMetricMatrixField4 g y)⁻¹ (physicalF.field y))
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus) z := by
  rw [isActualMetricActiveFourthOrderWedgeAt_iff_physicalMaxwellComplexion
    g choice physicalF physicalG a z hopen hz hLSmooth hqSmooth
      hupstream hstress hphysicalHodge hclosure]
  unfold IsPhysicalMaxwellComplexionActiveWedgeAt
  apply iff_of_eq
  exact congrArg (fun S => IsCoordinateMaxwellStressActiveWedge S
    (coordinatePhysicalComplexionOneForm
      (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
      physicalF.field physicalG.field
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) z)
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z)) (hstress z hz).symm

/-- **Fully physical scalar-orbit active locus.**  After identifying the
selected scalar with either orientation of a physical scalar covector, the
right-hand genericity predicate is made only from the inverse metric,
physical Maxwell/Hodge pair, physical Maxwell stress, `q`, and that physical
scalar. -/
theorem isActualMetricActiveFourthOrderWedgeAt_iff_choiceFreePhysicalScalarOrbit
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (physicalV : CurvatureCoordinateSpace4 → OneForm4)
    (a : ℝ) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hLSmooth : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hqSmooth : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y)))
    (hscalar :
      actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z = physicalV z ∨
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z = -physicalV z) :
    IsActualMetricActiveFourthOrderWedgeAt g z choice ↔
      IsPhysicalMaxwellComplexionActiveWedgeAt
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
        physicalF.field physicalG.field
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g))
        (fun y ↦ matrixMaxwellStress
          (coordinateMetricMatrixField4 g y)⁻¹ (physicalF.field y))
        physicalV z := by
  rw [isActualMetricActiveFourthOrderWedgeAt_iff_choiceFreePhysicalComplexion
    g choice physicalF physicalG a z hopen hz hLSmooth hqSmooth
      hupstream hstress hphysicalHodge hclosure]
  unfold IsPhysicalMaxwellComplexionActiveWedgeAt
  rcases hscalar with hplus | hminus
  · rw [hplus]
  · rw [hminus]
    exact isCoordinateMaxwellStressActiveWedge_neg_scalar
      (matrixMaxwellStress (coordinateMetricMatrixField4 g z)⁻¹
        (physicalF.field z))
      (coordinatePhysicalComplexionOneForm
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
        physicalF.field physicalG.field
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z)
      (physicalV z)

end RainichKaluza
