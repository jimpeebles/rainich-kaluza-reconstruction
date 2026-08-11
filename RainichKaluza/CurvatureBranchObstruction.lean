import RainichKaluza.SmoothCurvatureProjector

/-!
# Exact curvature branch obstruction

The smooth generic-patch construction produces two scalar candidates with
exterior derivatives `dalpha + dbeta` and `dalpha - dbeta`.  This file turns
those matrices into an exhaustive branch decision.

There are exactly four outcomes:

* only the sum branch closes, precisely when `dalpha = -dbeta` and
  `dalpha != 0`;
* only the difference branch closes, precisely when `dalpha = dbeta` and
  `dalpha != 0`;
* both close, precisely on the separately integrable locus
  `dalpha = dbeta = 0`;
* neither closes, precisely when `dalpha` equals neither `dbeta` nor
  `-dbeta`.

The patch-level version supplies finite witnesses that reject both local
branches.  It does not assume universal branch existence: failure of both
relations is the sharp curvature obstruction returned by the classifier.
-/

namespace RainichKaluza

open scoped Matrix

namespace CurvatureScalarBranchJet4

/-- The relative-sign sum candidate is closed at this curvature jet. -/
def PlusClosed (J : CurvatureScalarBranchJet4) : Prop :=
  oneFormJetExteriorDerivative J.vPlusJet = 0

/-- The relative-sign difference candidate is closed at this curvature jet. -/
def MinusClosed (J : CurvatureScalarBranchJet4) : Prop :=
  oneFormJetExteriorDerivative J.vMinusJet = 0

/-- Exactly the sum candidate closes. -/
def PlusOnly (J : CurvatureScalarBranchJet4) : Prop :=
  J.PlusClosed ∧ ¬J.MinusClosed

/-- Exactly the difference candidate closes. -/
def MinusOnly (J : CurvatureScalarBranchJet4) : Prop :=
  ¬J.PlusClosed ∧ J.MinusClosed

/-- Both candidates close. -/
def BothClosed (J : CurvatureScalarBranchJet4) : Prop :=
  J.PlusClosed ∧ J.MinusClosed

/-- Neither candidate closes. -/
def NeitherClosed (J : CurvatureScalarBranchJet4) : Prop :=
  ¬J.PlusClosed ∧ ¬J.MinusClosed

/-- The sum branch closes exactly when the two component obstructions are
opposites. -/
theorem plusClosed_iff (J : CurvatureScalarBranchJet4) :
    J.PlusClosed ↔ J.dalpha = -J.dbeta := by
  rw [PlusClosed, J.vPlus_exterior]
  exact add_eq_zero_iff_eq_neg

/-- The difference branch closes exactly when the two component obstructions
are equal. -/
theorem minusClosed_iff (J : CurvatureScalarBranchJet4) :
    J.MinusClosed ↔ J.dalpha = J.dbeta := by
  rw [MinusClosed, J.vMinus_exterior]
  exact sub_eq_zero

/-- **Unique sum-branch criterion.** -/
theorem plusOnly_iff (J : CurvatureScalarBranchJet4) :
    J.PlusOnly ↔ J.dalpha = -J.dbeta ∧ J.dalpha ≠ 0 := by
  constructor
  · rintro ⟨hplus, hnotminus⟩
    have hopposite := J.plusClosed_iff.mp hplus
    refine ⟨hopposite, ?_⟩
    intro hzero
    have hbeta : J.dbeta = 0 := by
      rw [hzero] at hopposite
      simpa using hopposite.symm
    exact hnotminus <| J.minusClosed_iff.mpr (by rw [hzero, hbeta])
  · rintro ⟨hopposite, hnonzero⟩
    refine ⟨J.plusClosed_iff.mpr hopposite, ?_⟩
    intro hminus
    have hboth : J.dalpha = 0 ∧ J.dbeta = 0 :=
      J.both_branches_closed_iff.mp
        ⟨J.plusClosed_iff.mpr hopposite, hminus⟩
    exact hnonzero hboth.1

/-- **Unique difference-branch criterion.** -/
theorem minusOnly_iff (J : CurvatureScalarBranchJet4) :
    J.MinusOnly ↔ J.dalpha = J.dbeta ∧ J.dalpha ≠ 0 := by
  constructor
  · rintro ⟨hnotplus, hminus⟩
    have hequal := J.minusClosed_iff.mp hminus
    refine ⟨hequal, ?_⟩
    intro hzero
    have hbeta : J.dbeta = 0 := by rw [← hequal, hzero]
    exact hnotplus <| J.plusClosed_iff.mpr (by rw [hzero, hbeta, neg_zero])
  · rintro ⟨hequal, hnonzero⟩
    refine ⟨?_, J.minusClosed_iff.mpr hequal⟩
    intro hplus
    have hboth : J.dalpha = 0 ∧ J.dbeta = 0 :=
      J.both_branches_closed_iff.mp
        ⟨hplus, J.minusClosed_iff.mpr hequal⟩
    exact hnonzero hboth.1

/-- **Two-branch exceptional locus.** Both scalar candidates close exactly
when the two spectral components are separately integrable. -/
theorem bothClosed_iff (J : CurvatureScalarBranchJet4) :
    J.BothClosed ↔ J.dalpha = 0 ∧ J.dbeta = 0 :=
  J.both_branches_closed_iff

/-- **Sharp no-branch obstruction.** Neither scalar candidate closes exactly
when the two curvature obstruction matrices are neither equal nor opposite. -/
theorem neitherClosed_iff (J : CurvatureScalarBranchJet4) :
    J.NeitherClosed ↔ J.dalpha ≠ -J.dbeta ∧ J.dalpha ≠ J.dbeta := by
  simp only [NeitherClosed, J.plusClosed_iff, J.minusClosed_iff]

/-- Every curvature branch jet lies in exactly one of the four closure
classes. -/
theorem exhaustive_closure_classification (J : CurvatureScalarBranchJet4) :
    J.PlusOnly ∨ J.MinusOnly ∨ J.BothClosed ∨ J.NeitherClosed := by
  classical
  by_cases hp : J.PlusClosed
  · by_cases hm : J.MinusClosed
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hm⟩))
    · exact Or.inl ⟨hp, hm⟩
  · by_cases hm : J.MinusClosed
    · exact Or.inr (Or.inl ⟨hp, hm⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hp, hm⟩))

/-- Discrete result returned by the curvature closure decision. -/
inductive ClosureOutcome where
  | plusOnly
  | minusOnly
  | both
  | neither
  deriving DecidableEq, Repr

/-- Computable-in-principle four-way branch decision. Equality of real
curvature data is classical, so the definition is intentionally
noncomputable. -/
noncomputable def closureOutcome (J : CurvatureScalarBranchJet4) :
    ClosureOutcome := by
  classical
  exact if J.PlusClosed then
    if J.MinusClosed then .both else .plusOnly
  else if J.MinusClosed then .minusOnly else .neither

theorem closureOutcome_eq_plusOnly_iff (J : CurvatureScalarBranchJet4) :
    J.closureOutcome = .plusOnly ↔ J.PlusOnly := by
  classical
  by_cases hp : J.PlusClosed <;> by_cases hm : J.MinusClosed <;>
    simp [closureOutcome, PlusOnly, hp, hm]

theorem closureOutcome_eq_minusOnly_iff (J : CurvatureScalarBranchJet4) :
    J.closureOutcome = .minusOnly ↔ J.MinusOnly := by
  classical
  by_cases hp : J.PlusClosed <;> by_cases hm : J.MinusClosed <;>
    simp [closureOutcome, MinusOnly, hp, hm]

theorem closureOutcome_eq_both_iff (J : CurvatureScalarBranchJet4) :
    J.closureOutcome = .both ↔ J.BothClosed := by
  classical
  by_cases hp : J.PlusClosed <;> by_cases hm : J.MinusClosed <;>
    simp [closureOutcome, BothClosed, hp, hm]

theorem closureOutcome_eq_neither_iff (J : CurvatureScalarBranchJet4) :
    J.closureOutcome = .neither ↔ J.NeitherClosed := by
  classical
  by_cases hp : J.PlusClosed <;> by_cases hm : J.MinusClosed <;>
    simp [closureOutcome, NeitherClosed, hp, hm]

end CurvatureScalarBranchJet4

section PatchClassification

variable {Y : Type*}

/-- The sum branch closes at every point of a patch. -/
def CurvaturePlusBranchClosesOn
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y) : Prop :=
  ∀ z ∈ U, (J z).PlusClosed

/-- The difference branch closes at every point of a patch. -/
def CurvatureMinusBranchClosesOn
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y) : Prop :=
  ∀ z ∈ U, (J z).MinusClosed

/-- The sum branch closes on a patch exactly when `dalpha=-dbeta`
pointwise. -/
theorem curvaturePlusBranchClosesOn_iff
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y) :
    CurvaturePlusBranchClosesOn J U ↔
      ∀ z ∈ U, (J z).dalpha = -(J z).dbeta := by
  constructor <;> intro h z hz
  · exact (J z).plusClosed_iff.mp (h z hz)
  · exact (J z).plusClosed_iff.mpr (h z hz)

/-- The difference branch closes on a patch exactly when `dalpha=dbeta`
pointwise. -/
theorem curvatureMinusBranchClosesOn_iff
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y) :
    CurvatureMinusBranchClosesOn J U ↔
      ∀ z ∈ U, (J z).dalpha = (J z).dbeta := by
  constructor <;> intro h z hz
  · exact (J z).minusClosed_iff.mp (h z hz)
  · exact (J z).minusClosed_iff.mpr (h z hz)

/-- Both branches close throughout a patch exactly when both component
obstructions vanish throughout it. -/
theorem both_curvatureBranches_closeOn_iff
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y) :
    (CurvaturePlusBranchClosesOn J U ∧
        CurvatureMinusBranchClosesOn J U) ↔
      ∀ z ∈ U, (J z).dalpha = 0 ∧ (J z).dbeta = 0 := by
  constructor
  · rintro ⟨hp, hm⟩ z hz
    exact (J z).bothClosed_iff.mp ⟨hp z hz, hm z hz⟩
  · intro h
    constructor <;> intro z hz
    · exact (J z).bothClosed_iff.mpr (h z hz) |>.1
    · exact (J z).bothClosed_iff.mpr (h z hz) |>.2

/-- A point where `dalpha+dbeta` is nonzero rejects the sum branch on the
whole patch. -/
theorem not_curvaturePlusBranchClosesOn_of_witness
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y)
    {z : Y} (hz : z ∈ U)
    (hobs : (J z).dalpha + (J z).dbeta ≠ 0) :
    ¬CurvaturePlusBranchClosesOn J U := by
  intro hplus
  have hzero := hplus z hz
  change oneFormJetExteriorDerivative (J z).vPlusJet = 0 at hzero
  rw [(J z).vPlus_exterior] at hzero
  exact hobs hzero

/-- A point where `dalpha-dbeta` is nonzero rejects the difference branch on
the whole patch. -/
theorem not_curvatureMinusBranchClosesOn_of_witness
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y)
    {z : Y} (hz : z ∈ U)
    (hobs : (J z).dalpha - (J z).dbeta ≠ 0) :
    ¬CurvatureMinusBranchClosesOn J U := by
  intro hminus
  have hzero := hminus z hz
  change oneFormJetExteriorDerivative (J z).vMinusJet = 0 at hzero
  rw [(J z).vMinus_exterior] at hzero
  exact hobs hzero

/-- **Patch-level no-branch certificate.** Separate finite witnesses for the
two obstruction matrices prove that neither relative-sign scalar branch can
be closed on the patch.  The witnesses may occur at different points. -/
theorem neither_curvatureBranch_closesOn_of_witnesses
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y)
    {zPlus zMinus : Y} (hzPlus : zPlus ∈ U) (hzMinus : zMinus ∈ U)
    (hplus : (J zPlus).dalpha + (J zPlus).dbeta ≠ 0)
    (hminus : (J zMinus).dalpha - (J zMinus).dbeta ≠ 0) :
    ¬CurvaturePlusBranchClosesOn J U ∧
      ¬CurvatureMinusBranchClosesOn J U :=
  ⟨not_curvaturePlusBranchClosesOn_of_witness J U hzPlus hplus,
    not_curvatureMinusBranchClosesOn_of_witness J U hzMinus hminus⟩

/-- The two patch-level candidates also admit an exhaustive closure
classification, with no assumption that one of them exists. -/
theorem exhaustive_patch_closure_classification
    (J : Y → CurvatureScalarBranchJet4) (U : Set Y) :
    (CurvaturePlusBranchClosesOn J U ∧
        ¬CurvatureMinusBranchClosesOn J U) ∨
      (¬CurvaturePlusBranchClosesOn J U ∧
        CurvatureMinusBranchClosesOn J U) ∨
      (CurvaturePlusBranchClosesOn J U ∧
        CurvatureMinusBranchClosesOn J U) ∨
      (¬CurvaturePlusBranchClosesOn J U ∧
        ¬CurvatureMinusBranchClosesOn J U) := by
  classical
  by_cases hp : CurvaturePlusBranchClosesOn J U
  · by_cases hm : CurvatureMinusBranchClosesOn J U
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hm⟩))
    · exact Or.inl ⟨hp, hm⟩
  · by_cases hm : CurvatureMinusBranchClosesOn J U
    · exact Or.inr (Or.inl ⟨hp, hm⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hp, hm⟩))

end PatchClassification

end RainichKaluza
