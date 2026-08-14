import RainichKaluza.CouplingPhasePropagation
import RainichKaluza.CurvatureBranchIntegration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Local half-angle lift

This file supplies the local algebraic half-angle seam used by the proposed
Kaluza converse.  If the propagated double-angle components satisfy

`A² + B² = a²`, with `a > 0`, then away from the two usual chart cuts they
have explicit lifts `(c,s)` with

`c² + s² = 1`, `A = a (c² - s²)`, and `B = 2 a c s`.

The positive-cosine chart excludes `A = -a`; the positive-sine chart excludes
`A = a`.  These exclusions make the square-root arguments *strictly*
positive.  They are therefore also the honest hypotheses needed for smooth
square-root differentiation, not merely algebraic denominator conditions.

The final section proves the chart-independent first-jet linear algebra: if
the derivatives of the reconstructed double-angle components obey the two
phase laws, then necessarily `dc = -s omega` and `ds = c omega`.
-/

namespace RainichKaluza

/-! ## Positive-cosine chart -/

/-- Cosine coordinate on the half-angle chart `A ≠ -a`. -/
noncomputable def positiveCosineHalfAngleC (a A : ℝ) : ℝ :=
  Real.sqrt ((a + A) / (2 * a))

/-- Sine coordinate on the half-angle chart `A ≠ -a`, with its sign fixed
by the signed double-angle sine component `B`. -/
noncomputable def positiveCosineHalfAngleS (a A B : ℝ) : ℝ :=
  B / (2 * a * positiveCosineHalfAngleC a A)

/-- On the coupling circle, the positive-cosine square-root argument is
strictly positive precisely after excluding the endpoint `A = -a`. -/
theorem positiveCosineHalfAngle_argument_pos
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ -a) :
    0 < (a + A) / (2 * a) := by
  have hsq : A ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg B]
  have hlower : -a ≤ A := by
    by_contra h
    have hlt : A < -a := lt_of_not_ge h
    nlinarith [sq_nonneg (A + a)]
  have hsum_nonneg : 0 ≤ a + A := by linarith
  have hsum_ne : a + A ≠ 0 := by
    intro hzero
    apply hchart
    linarith
  have hsum_pos : 0 < a + A :=
    lt_of_le_of_ne hsum_nonneg (Ne.symm hsum_ne)
  exact div_pos hsum_pos (mul_pos (by norm_num) ha)

/-- The selected cosine is strictly positive on its chart. -/
theorem positiveCosineHalfAngleC_pos
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ -a) :
    0 < positiveCosineHalfAngleC a A := by
  exact Real.sqrt_pos.2
    (positiveCosineHalfAngle_argument_pos a A B ha hcircle hchart)

/-- Square of the selected positive cosine. -/
theorem positiveCosineHalfAngleC_sq
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ -a) :
    (positiveCosineHalfAngleC a A) ^ 2 = (a + A) / (2 * a) := by
  exact Real.sq_sqrt (le_of_lt
    (positiveCosineHalfAngle_argument_pos a A B ha hcircle hchart))

/-- The positive-cosine chart reproduces the signed sine component. -/
theorem positiveCosineHalfAngle_sineComponent
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ -a) :
    B = 2 * a * positiveCosineHalfAngleC a A *
      positiveCosineHalfAngleS a A B := by
  have hc : positiveCosineHalfAngleC a A ≠ 0 :=
    ne_of_gt (positiveCosineHalfAngleC_pos a A B ha hcircle hchart)
  unfold positiveCosineHalfAngleS
  field_simp [ha.ne', hc]

/-- The positive-cosine chart lies on the unit circle. -/
theorem positiveCosineHalfAngle_unit
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ -a) :
    (positiveCosineHalfAngleC a A) ^ 2 +
      (positiveCosineHalfAngleS a A B) ^ 2 = 1 := by
  have hc : positiveCosineHalfAngleC a A ≠ 0 :=
    ne_of_gt (positiveCosineHalfAngleC_pos a A B ha hcircle hchart)
  have hcsq := positiveCosineHalfAngleC_sq a A B ha hcircle hchart
  have htwoc :
      2 * a * (positiveCosineHalfAngleC a A) ^ 2 = a + A := by
    field_simp [ha.ne'] at hcsq
    linarith
  have htwocSq := congrArg (fun x : ℝ => x ^ 2) htwoc
  unfold positiveCosineHalfAngleS
  field_simp [ha.ne', hc]
  nlinarith [htwocSq]

/-- The positive-cosine chart reproduces the signed cosine component. -/
theorem positiveCosineHalfAngle_cosineComponent
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ -a) :
    A = a * ((positiveCosineHalfAngleC a A) ^ 2 -
      (positiveCosineHalfAngleS a A B) ^ 2) := by
  have hunit := positiveCosineHalfAngle_unit a A B ha hcircle hchart
  have hcsq := positiveCosineHalfAngleC_sq a A B ha hcircle hchart
  field_simp [ha.ne'] at hcsq
  nlinarith

/-- Complete algebraic specification of the positive-cosine half-angle lift. -/
theorem positiveCosineHalfAngle_spec
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ -a) :
    (positiveCosineHalfAngleC a A) ^ 2 +
          (positiveCosineHalfAngleS a A B) ^ 2 = 1 ∧
      A = a * ((positiveCosineHalfAngleC a A) ^ 2 -
          (positiveCosineHalfAngleS a A B) ^ 2) ∧
      B = 2 * a * positiveCosineHalfAngleC a A *
          positiveCosineHalfAngleS a A B := by
  exact ⟨positiveCosineHalfAngle_unit a A B ha hcircle hchart,
    positiveCosineHalfAngle_cosineComponent a A B ha hcircle hchart,
    positiveCosineHalfAngle_sineComponent a A B ha hcircle hchart⟩

/-! ## Positive-sine chart -/

/-- Sine coordinate on the complementary half-angle chart `A ≠ a`. -/
noncomputable def positiveSineHalfAngleS (a A : ℝ) : ℝ :=
  Real.sqrt ((a - A) / (2 * a))

/-- Cosine coordinate on the half-angle chart `A ≠ a`, with its sign fixed
by the signed double-angle sine component `B`. -/
noncomputable def positiveSineHalfAngleC (a A B : ℝ) : ℝ :=
  B / (2 * a * positiveSineHalfAngleS a A)

/-- On the coupling circle, the positive-sine square-root argument is
strictly positive after excluding the endpoint `A = a`. -/
theorem positiveSineHalfAngle_argument_pos
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ a) :
    0 < (a - A) / (2 * a) := by
  have hsq : A ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg B]
  have hupper : A ≤ a := by
    by_contra h
    have hlt : a < A := lt_of_not_ge h
    nlinarith [sq_nonneg (A - a)]
  have hdiff_nonneg : 0 ≤ a - A := by linarith
  have hdiff_ne : a - A ≠ 0 := by
    intro hzero
    apply hchart
    linarith
  have hdiff_pos : 0 < a - A :=
    lt_of_le_of_ne hdiff_nonneg (Ne.symm hdiff_ne)
  exact div_pos hdiff_pos (mul_pos (by norm_num) ha)

/-- The selected sine is strictly positive on its chart. -/
theorem positiveSineHalfAngleS_pos
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ a) :
    0 < positiveSineHalfAngleS a A := by
  exact Real.sqrt_pos.2
    (positiveSineHalfAngle_argument_pos a A B ha hcircle hchart)

/-- Square of the selected positive sine. -/
theorem positiveSineHalfAngleS_sq
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ a) :
    (positiveSineHalfAngleS a A) ^ 2 = (a - A) / (2 * a) := by
  exact Real.sq_sqrt (le_of_lt
    (positiveSineHalfAngle_argument_pos a A B ha hcircle hchart))

/-- The positive-sine chart reproduces the signed sine component. -/
theorem positiveSineHalfAngle_sineComponent
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ a) :
    B = 2 * a * positiveSineHalfAngleC a A B *
      positiveSineHalfAngleS a A := by
  have hs : positiveSineHalfAngleS a A ≠ 0 :=
    ne_of_gt (positiveSineHalfAngleS_pos a A B ha hcircle hchart)
  unfold positiveSineHalfAngleC
  field_simp [ha.ne', hs]

/-- The positive-sine chart lies on the unit circle. -/
theorem positiveSineHalfAngle_unit
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ a) :
    (positiveSineHalfAngleC a A B) ^ 2 +
      (positiveSineHalfAngleS a A) ^ 2 = 1 := by
  have hs : positiveSineHalfAngleS a A ≠ 0 :=
    ne_of_gt (positiveSineHalfAngleS_pos a A B ha hcircle hchart)
  have hssq := positiveSineHalfAngleS_sq a A B ha hcircle hchart
  have htwos :
      2 * a * (positiveSineHalfAngleS a A) ^ 2 = a - A := by
    field_simp [ha.ne'] at hssq
    linarith
  have htwosSq := congrArg (fun x : ℝ => x ^ 2) htwos
  unfold positiveSineHalfAngleC
  field_simp [ha.ne', hs]
  nlinarith [htwosSq]

/-- The positive-sine chart reproduces the signed cosine component. -/
theorem positiveSineHalfAngle_cosineComponent
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ a) :
    A = a * ((positiveSineHalfAngleC a A B) ^ 2 -
      (positiveSineHalfAngleS a A) ^ 2) := by
  have hunit := positiveSineHalfAngle_unit a A B ha hcircle hchart
  have hssq := positiveSineHalfAngleS_sq a A B ha hcircle hchart
  field_simp [ha.ne'] at hssq
  nlinarith

/-- Complete algebraic specification of the positive-sine half-angle lift. -/
theorem positiveSineHalfAngle_spec
    (a A B : ℝ) (ha : 0 < a)
    (hcircle : A ^ 2 + B ^ 2 = a ^ 2) (hchart : A ≠ a) :
    (positiveSineHalfAngleC a A B) ^ 2 +
          (positiveSineHalfAngleS a A) ^ 2 = 1 ∧
      A = a * ((positiveSineHalfAngleC a A B) ^ 2 -
          (positiveSineHalfAngleS a A) ^ 2) ∧
      B = 2 * a * positiveSineHalfAngleC a A B *
          positiveSineHalfAngleS a A := by
  exact ⟨positiveSineHalfAngle_unit a A B ha hcircle hchart,
    positiveSineHalfAngle_cosineComponent a A B ha hcircle hchart,
    positiveSineHalfAngle_sineComponent a A B ha hcircle hchart⟩

/-! ## Smoothness on a chart patch -/

/-- The positive-cosine coordinate is as smooth as `A` on a patch on which
the coupling circle holds and the excluded endpoint is absent.  The proof
uses strict positivity of the square-root argument at every patch point. -/
theorem contDiffOn_positiveCosineHalfAngleC
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} (a : ℝ) {A B : X → ℝ}
    (ha : 0 < a) (hA : ContDiffOn ℝ n A U)
    (hcircle : ∀ z ∈ U, (A z) ^ 2 + (B z) ^ 2 = a ^ 2)
    (hchart : ∀ z ∈ U, A z ≠ -a) :
    ContDiffOn ℝ n (fun z => positiveCosineHalfAngleC a (A z)) U := by
  have harg : ContDiffOn ℝ n (fun z => (a + A z) / (2 * a)) U :=
    (contDiffOn_const.add hA).div_const (2 * a)
  exact harg.sqrt (fun z hz => ne_of_gt
    (positiveCosineHalfAngle_argument_pos a (A z) (B z) ha
      (hcircle z hz) (hchart z hz)))

/-- The signed sine coordinate is smooth on the positive-cosine chart. -/
theorem contDiffOn_positiveCosineHalfAngleS
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} (a : ℝ) {A B : X → ℝ}
    (ha : 0 < a) (hA : ContDiffOn ℝ n A U)
    (hB : ContDiffOn ℝ n B U)
    (hcircle : ∀ z ∈ U, (A z) ^ 2 + (B z) ^ 2 = a ^ 2)
    (hchart : ∀ z ∈ U, A z ≠ -a) :
    ContDiffOn ℝ n
      (fun z => positiveCosineHalfAngleS a (A z) (B z)) U := by
  have hc := contDiffOn_positiveCosineHalfAngleC a ha hA hcircle hchart
  change ContDiffOn ℝ n
    (fun z => B z / (2 * a * positiveCosineHalfAngleC a (A z))) U
  exact hB.div (contDiffOn_const.mul hc) (fun z hz => mul_ne_zero
    (mul_ne_zero (by norm_num) ha.ne')
    (ne_of_gt (positiveCosineHalfAngleC_pos a (A z) (B z) ha
      (hcircle z hz) (hchart z hz))))

/-- Both fields in the positive-cosine lift are smooth on their chart. -/
theorem contDiffOn_positiveCosineHalfAngleLift
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} (a : ℝ) {A B : X → ℝ}
    (ha : 0 < a) (hA : ContDiffOn ℝ n A U)
    (hB : ContDiffOn ℝ n B U)
    (hcircle : ∀ z ∈ U, (A z) ^ 2 + (B z) ^ 2 = a ^ 2)
    (hchart : ∀ z ∈ U, A z ≠ -a) :
    ContDiffOn ℝ n (fun z => positiveCosineHalfAngleC a (A z)) U ∧
      ContDiffOn ℝ n
        (fun z => positiveCosineHalfAngleS a (A z) (B z)) U := by
  exact ⟨contDiffOn_positiveCosineHalfAngleC a ha hA hcircle hchart,
    contDiffOn_positiveCosineHalfAngleS a ha hA hB hcircle hchart⟩

/-- The positive-sine coordinate is as smooth as `A` on its complementary
chart. -/
theorem contDiffOn_positiveSineHalfAngleS
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} (a : ℝ) {A B : X → ℝ}
    (ha : 0 < a) (hA : ContDiffOn ℝ n A U)
    (hcircle : ∀ z ∈ U, (A z) ^ 2 + (B z) ^ 2 = a ^ 2)
    (hchart : ∀ z ∈ U, A z ≠ a) :
    ContDiffOn ℝ n (fun z => positiveSineHalfAngleS a (A z)) U := by
  have harg : ContDiffOn ℝ n (fun z => (a - A z) / (2 * a)) U :=
    (contDiffOn_const.sub hA).div_const (2 * a)
  exact harg.sqrt (fun z hz => ne_of_gt
    (positiveSineHalfAngle_argument_pos a (A z) (B z) ha
      (hcircle z hz) (hchart z hz)))

/-- The signed cosine coordinate is smooth on the positive-sine chart. -/
theorem contDiffOn_positiveSineHalfAngleC
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} (a : ℝ) {A B : X → ℝ}
    (ha : 0 < a) (hA : ContDiffOn ℝ n A U)
    (hB : ContDiffOn ℝ n B U)
    (hcircle : ∀ z ∈ U, (A z) ^ 2 + (B z) ^ 2 = a ^ 2)
    (hchart : ∀ z ∈ U, A z ≠ a) :
    ContDiffOn ℝ n
      (fun z => positiveSineHalfAngleC a (A z) (B z)) U := by
  have hs := contDiffOn_positiveSineHalfAngleS a ha hA hcircle hchart
  change ContDiffOn ℝ n
    (fun z => B z / (2 * a * positiveSineHalfAngleS a (A z))) U
  exact hB.div (contDiffOn_const.mul hs) (fun z hz => mul_ne_zero
    (mul_ne_zero (by norm_num) ha.ne')
    (ne_of_gt (positiveSineHalfAngleS_pos a (A z) (B z) ha
      (hcircle z hz) (hchart z hz))))

/-- Both fields in the positive-sine lift are smooth on their chart. -/
theorem contDiffOn_positiveSineHalfAngleLift
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} (a : ℝ) {A B : X → ℝ}
    (ha : 0 < a) (hA : ContDiffOn ℝ n A U)
    (hB : ContDiffOn ℝ n B U)
    (hcircle : ∀ z ∈ U, (A z) ^ 2 + (B z) ^ 2 = a ^ 2)
    (hchart : ∀ z ∈ U, A z ≠ a) :
    ContDiffOn ℝ n
        (fun z => positiveSineHalfAngleC a (A z) (B z)) U ∧
      ContDiffOn ℝ n (fun z => positiveSineHalfAngleS a (A z)) U := by
  exact ⟨contDiffOn_positiveSineHalfAngleC a ha hA hB hcircle hchart,
    contDiffOn_positiveSineHalfAngleS a ha hA hcircle hchart⟩

/-! ## Chart-independent first-jet reconstruction -/

/-- If a unit-circle lift differentiates the reconstructed double-angle
components and those components obey the two phase laws, its first jet is
forced to be the usual phase rotation.  This is pointwise algebra and does
not assume that arbitrary prescribed covectors are derivatives of fields. -/
theorem halfAngleFirstDerivatives_eq_phaseLaws
    (a c s A B : ℝ) (dc ds dA dB omega : OneForm4)
    (ha : a ≠ 0) (hunit : c ^ 2 + s ^ 2 = 1)
    (hA : A = a * (c ^ 2 - s ^ 2))
    (hB : B = 2 * a * c * s)
    (hdA_reconstruct :
      dA = doubleAngleCosineFirstDerivative a c s dc ds)
    (hdB_reconstruct :
      dB = doubleAngleSineFirstDerivative a c s dc ds)
    (hdA_phase : dA = (-2 * B) • omega)
    (hdB_phase : dB = (2 * A) • omega) :
    dc = (-s) • omega ∧ ds = c • omega := by
  constructor <;> funext i
  · have hda := congrFun (hdA_reconstruct.symm.trans hdA_phase) i
    have hdb := congrFun (hdB_reconstruct.symm.trans hdB_phase) i
    simp only [doubleAngleCosineFirstDerivative,
      doubleAngleSineFirstDerivative, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hda hdb
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hB] at hda
    rw [hA] at hdb
    have hscaled : a * (dc i + s * omega i) = 0 := by
      calc
        a * (dc i + s * omega i) =
            a * (c ^ 2 + s ^ 2) * dc i + a * s * omega i := by
              rw [hunit]
              ring
        _ = c / 2 * (2 * a * c * dc i - 2 * a * s * ds i) +
              s / 2 * (2 * a * s * dc i + 2 * a * c * ds i) +
              a * s * omega i := by ring
        _ = c / 2 * (-2 * (2 * a * c * s) * omega i) +
              s / 2 * (2 * (a * (c ^ 2 - s ^ 2)) * omega i) +
              a * s * omega i := by rw [hda, hdb]
        _ = a * s * (1 - (c ^ 2 + s ^ 2)) * omega i := by ring
        _ = 0 := by rw [hunit]; ring
    have hz := (mul_eq_zero.mp hscaled).resolve_left ha
    linarith
  · have hda := congrFun (hdA_reconstruct.symm.trans hdA_phase) i
    have hdb := congrFun (hdB_reconstruct.symm.trans hdB_phase) i
    simp only [doubleAngleCosineFirstDerivative,
      doubleAngleSineFirstDerivative, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hda hdb
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hB] at hda
    rw [hA] at hdb
    have hscaled : a * (ds i - c * omega i) = 0 := by
      calc
        a * (ds i - c * omega i) =
            a * (c ^ 2 + s ^ 2) * ds i - a * c * omega i := by
              rw [hunit]
              ring
        _ = -(s / 2) * (2 * a * c * dc i - 2 * a * s * ds i) +
              c / 2 * (2 * a * s * dc i + 2 * a * c * ds i) -
              a * c * omega i := by ring
        _ = -(s / 2) * (-2 * (2 * a * c * s) * omega i) +
              c / 2 * (2 * (a * (c ^ 2 - s ^ 2)) * omega i) -
              a * c * omega i := by rw [hda, hdb]
        _ = a * c * ((c ^ 2 + s ^ 2) - 1) * omega i := by ring
        _ = 0 := by rw [hunit]; ring
    have hz := (mul_eq_zero.mp hscaled).resolve_left ha
    linarith

/-! ## Actual coordinate derivatives on a smooth patch -/

/-- Field-level form of the half-angle derivative theorem.  Smooth local
fields `(c,s)` which reconstruct `(A,B)` on an open patch have actual
coordinate Frechet derivatives obeying the phase rotation whenever the
actual derivatives of `(A,B)` obey the propagated phase laws.

The local reconstruction hypotheses are what connect the displayed
covectors to genuine derivatives; no formal first jet is silently treated as
integrable. -/
theorem localHalfAngleCoordinateFDerivatives_eq_phaseLaws
    {U : Set CurvatureCoordinateSpace4}
    (hopen : IsOpen U) (z : CurvatureCoordinateSpace4) (hz : z ∈ U)
    (a : ℝ) (A B c s : CurvatureCoordinateSpace4 → ℝ)
    (omega : OneForm4) (ha : a ≠ 0)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U)
    (hunit : (c z) ^ 2 + (s z) ^ 2 = 1)
    (hA_local : ∀ y ∈ U, A y = a * ((c y) ^ 2 - (s y) ^ 2))
    (hB_local : ∀ y ∈ U, B y = 2 * a * c y * s y)
    (hdA_phase : scalarFieldCoordinateFDeriv A z =
      (-2 * B z) • omega)
    (hdB_phase : scalarFieldCoordinateFDeriv B z =
      (2 * A z) • omega) :
    scalarFieldCoordinateFDeriv c z = (-s z) • omega ∧
      scalarFieldCoordinateFDeriv s z = c z • omega := by
  have hcdiff : DifferentiableAt ℝ c z :=
    (hc.differentiableOn_one z hz).differentiableAt (hopen.mem_nhds hz)
  have hsdiff : DifferentiableAt ℝ s z :=
    (hs.differentiableOn_one z hz).differentiableAt (hopen.mem_nhds hz)
  have hAevent : Filter.EventuallyEq (nhds z) A
      (fun y => a * ((c y) ^ 2 - (s y) ^ 2)) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact hA_local y hy
  have hBevent : Filter.EventuallyEq (nhds z) B
      (fun y => 2 * a * c y * s y) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact hB_local y hy
  have hdA_reconstruct :
      scalarFieldCoordinateFDeriv A z =
        doubleAngleCosineFirstDerivative a (c z) (s z)
          (scalarFieldCoordinateFDeriv c z)
          (scalarFieldCoordinateFDeriv s z) := by
    funext r
    unfold scalarFieldCoordinateFDeriv doubleAngleCosineFirstDerivative
    rw [Filter.EventuallyEq.fderiv_eq hAevent]
    simp only [pow_two]
    change (fderiv ℝ (fun y => a * ((c * c - s * s) y)) z)
        (curvatureCoordinateDirection r) = _
    rw [fderiv_const_mul ((hcdiff.mul hcdiff).sub
      (hsdiff.mul hsdiff)) a]
    rw [fderiv_sub (hcdiff.mul hcdiff) (hsdiff.mul hsdiff)]
    rw [fderiv_mul hcdiff hcdiff, fderiv_mul hsdiff hsdiff]
    simp only [smul_apply, sub_apply, Pi.sub_apply, Pi.smul_apply,
      add_apply, smul_eq_mul]
    ring_nf
  have hdB_reconstruct :
      scalarFieldCoordinateFDeriv B z =
        doubleAngleSineFirstDerivative a (c z) (s z)
          (scalarFieldCoordinateFDeriv c z)
          (scalarFieldCoordinateFDeriv s z) := by
    funext r
    unfold scalarFieldCoordinateFDeriv doubleAngleSineFirstDerivative
    rw [Filter.EventuallyEq.fderiv_eq hBevent]
    rw [show (fun y => 2 * a * c y * s y) =
        (fun y => (2 * a) * ((c * s) y)) by
      funext y
      change 2 * a * c y * s y = (2 * a) * (c y * s y)
      ring]
    rw [fderiv_const_mul (hcdiff.mul hsdiff) (2 * a)]
    rw [fderiv_mul hcdiff hsdiff]
    simp only [smul_apply, add_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring_nf
  exact halfAngleFirstDerivatives_eq_phaseLaws a (c z) (s z)
    (A z) (B z) (scalarFieldCoordinateFDeriv c z)
    (scalarFieldCoordinateFDeriv s z)
    (scalarFieldCoordinateFDeriv A z)
    (scalarFieldCoordinateFDeriv B z) omega ha hunit
    (hA_local z hz) (hB_local z hz) hdA_reconstruct hdB_reconstruct
    hdA_phase hdB_phase

/-- On an open positive-cosine chart, the explicit smooth square-root lift
has the actual phase-law coordinate derivatives. -/
theorem positiveCosineHalfAngleCoordinateFDerivatives_eq_phaseLaws
    {U : Set CurvatureCoordinateSpace4}
    (hopen : IsOpen U) (z : CurvatureCoordinateSpace4) (hz : z ∈ U)
    (a : ℝ) (A B : CurvatureCoordinateSpace4 → ℝ)
    (omega : OneForm4) (ha : 0 < a)
    (hA : ContDiffOn ℝ 1 A U) (hB : ContDiffOn ℝ 1 B U)
    (hcircle : ∀ y ∈ U, (A y) ^ 2 + (B y) ^ 2 = a ^ 2)
    (hchart : ∀ y ∈ U, A y ≠ -a)
    (hdA_phase : scalarFieldCoordinateFDeriv A z =
      (-2 * B z) • omega)
    (hdB_phase : scalarFieldCoordinateFDeriv B z =
      (2 * A z) • omega) :
    scalarFieldCoordinateFDeriv
        (fun y => positiveCosineHalfAngleC a (A y)) z =
          (-positiveCosineHalfAngleS a (A z) (B z)) • omega ∧
      scalarFieldCoordinateFDeriv
        (fun y => positiveCosineHalfAngleS a (A y) (B y)) z =
          positiveCosineHalfAngleC a (A z) • omega := by
  apply localHalfAngleCoordinateFDerivatives_eq_phaseLaws hopen z hz a
    A B (fun y => positiveCosineHalfAngleC a (A y))
    (fun y => positiveCosineHalfAngleS a (A y) (B y)) omega ha.ne'
    (contDiffOn_positiveCosineHalfAngleC a ha hA hcircle hchart)
    (contDiffOn_positiveCosineHalfAngleS a ha hA hB hcircle hchart)
    (positiveCosineHalfAngle_unit a (A z) (B z) ha
      (hcircle z hz) (hchart z hz))
  · intro y hy
    exact positiveCosineHalfAngle_cosineComponent a (A y) (B y) ha
      (hcircle y hy) (hchart y hy)
  · intro y hy
    exact positiveCosineHalfAngle_sineComponent a (A y) (B y) ha
      (hcircle y hy) (hchart y hy)
  · exact hdA_phase
  · exact hdB_phase

/-- On an open positive-sine chart, the complementary explicit lift has the
actual phase-law coordinate derivatives. -/
theorem positiveSineHalfAngleCoordinateFDerivatives_eq_phaseLaws
    {U : Set CurvatureCoordinateSpace4}
    (hopen : IsOpen U) (z : CurvatureCoordinateSpace4) (hz : z ∈ U)
    (a : ℝ) (A B : CurvatureCoordinateSpace4 → ℝ)
    (omega : OneForm4) (ha : 0 < a)
    (hA : ContDiffOn ℝ 1 A U) (hB : ContDiffOn ℝ 1 B U)
    (hcircle : ∀ y ∈ U, (A y) ^ 2 + (B y) ^ 2 = a ^ 2)
    (hchart : ∀ y ∈ U, A y ≠ a)
    (hdA_phase : scalarFieldCoordinateFDeriv A z =
      (-2 * B z) • omega)
    (hdB_phase : scalarFieldCoordinateFDeriv B z =
      (2 * A z) • omega) :
    scalarFieldCoordinateFDeriv
        (fun y => positiveSineHalfAngleC a (A y) (B y)) z =
          (-positiveSineHalfAngleS a (A z)) • omega ∧
      scalarFieldCoordinateFDeriv
        (fun y => positiveSineHalfAngleS a (A y)) z =
          positiveSineHalfAngleC a (A z) (B z) • omega := by
  apply localHalfAngleCoordinateFDerivatives_eq_phaseLaws hopen z hz a
    A B (fun y => positiveSineHalfAngleC a (A y) (B y))
    (fun y => positiveSineHalfAngleS a (A y)) omega ha.ne'
    (contDiffOn_positiveSineHalfAngleC a ha hA hB hcircle hchart)
    (contDiffOn_positiveSineHalfAngleS a ha hA hcircle hchart)
    (positiveSineHalfAngle_unit a (A z) (B z) ha
      (hcircle z hz) (hchart z hz))
  · intro y hy
    exact positiveSineHalfAngle_cosineComponent a (A y) (B y) ha
      (hcircle y hy) (hchart y hy)
  · intro y hy
    exact positiveSineHalfAngle_sineComponent a (A y) (B y) ha
      (hcircle y hy) (hchart y hy)
  · exact hdA_phase
  · exact hdB_phase

end RainichKaluza
