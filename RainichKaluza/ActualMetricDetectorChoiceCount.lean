import RainichKaluza.FourthOrderMetricDetector

/-!
# Exact size of the actual-metric detector search space

This audit module records the cardinality of the explicit raw choice
enumeration used by `acceptedActualMetricFourthOrderDetectorChoicesAt`.
The result concerns raw choices before any metric-dependent acceptance gates
are applied.
-/

namespace RainichKaluza

/-- Product encoding of every field of `ActualMetricDetectorChoice4`. -/
private abbrev ActualMetricDetectorChoiceCode4 :=
  Fin 4 × Fin 4 × Fin 4 × Fin 4 × LorentzianPivotRecipe ×
    Fin 4 × Fin 4 × Bool × Bool × FourthOrderComponentChoice

/-- The product encoding contains exactly the same information as one raw
actual-metric detector choice. -/
private def actualMetricDetectorChoiceCodeEquiv :
    ActualMetricDetectorChoiceCode4 ≃ ActualMetricDetectorChoice4 where
  toFun
    | ⟨scalarTimelikeProbe, scalarSpacelikeProbe,
        maxwellMinusProbe0, maxwellMinusProbe1,
        maxwellMinusPivotRecipe, maxwellPlusProbe0, maxwellPlusProbe1,
        relativeMinus, orientationReverse, channel⟩ =>
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
  invFun choice :=
    ⟨choice.scalarTimelikeProbe, choice.scalarSpacelikeProbe,
      choice.maxwellMinusProbe0, choice.maxwellMinusProbe1,
      choice.maxwellMinusPivotRecipe, choice.maxwellPlusProbe0,
      choice.maxwellPlusProbe1, choice.relativeMinus,
      choice.orientationReverse, choice.channel⟩
  left_inv := by
    rintro ⟨scalarTimelikeProbe, scalarSpacelikeProbe,
      maxwellMinusProbe0, maxwellMinusProbe1,
      maxwellMinusPivotRecipe, maxwellPlusProbe0, maxwellPlusProbe1,
      relativeMinus, orientationReverse, channel⟩
    rfl
  right_inv := by
    rintro ⟨scalarTimelikeProbe, scalarSpacelikeProbe,
      maxwellMinusProbe0, maxwellMinusProbe1,
      maxwellMinusPivotRecipe, maxwellPlusProbe0, maxwellPlusProbe1,
      relativeMinus, orientationReverse, channel⟩
    rfl

/-- A finite-type instance justified by the transparent product encoding. -/
noncomputable instance : Fintype ActualMetricDetectorChoice4 :=
  Fintype.ofEquiv ActualMetricDetectorChoiceCode4
    actualMetricDetectorChoiceCodeEquiv

/-- The hand-written nested enumeration really contains every raw choice and
therefore agrees with `Finset.univ` for the explicit finite-type instance. -/
theorem allActualMetricDetectorChoices4_eq_univ :
    allActualMetricDetectorChoices4 =
      (Finset.univ : Finset ActualMetricDetectorChoice4) := by
  ext choice
  simp only [mem_allActualMetricDetectorChoices4, Finset.mem_univ]

private theorem lorentzianPivotRecipe_card :
    Fintype.card LorentzianPivotRecipe = 6 := by
  rfl

private theorem actualMetricDetectorChoiceCode4_card :
    Fintype.card ActualMetricDetectorChoiceCode4 = 6291456 := by
  simp [ActualMetricDetectorChoiceCode4, Fintype.card_prod,
    lorentzianPivotRecipe_card]

/-- **Exact raw detector-choice count.** The six coordinate-probe indices,
six Lorentzian pivot recipes, two relative-sign/orientation bits, and 64
source/wedge channels give exactly `6,291,456` raw choices before filtering. -/
theorem allActualMetricDetectorChoices4_card :
    allActualMetricDetectorChoices4.card = 6291456 := by
  rw [allActualMetricDetectorChoices4_eq_univ, Finset.card_univ]
  calc
    Fintype.card ActualMetricDetectorChoice4 =
        Fintype.card ActualMetricDetectorChoiceCode4 :=
      Fintype.card_congr actualMetricDetectorChoiceCodeEquiv.symm
    _ = 6291456 := actualMetricDetectorChoiceCode4_card

/-- Membership in the finite accepted set is the named complete metric-only
acceptance predicate, now paired locally with the exact raw search bound. -/
theorem mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff_completeAcceptance
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ↔
      IsActualMetricFourthOrderDetectorCandidateAt g z choice :=
  mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff g z choice

end RainichKaluza
