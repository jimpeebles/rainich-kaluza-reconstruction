import RainichKaluza.ThirdOrderMatterJetAmbiguity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Simple spectrum of the active formal metric-three-jet ambiguity

The active ambiguity uses a scalar covector supported in both Maxwell
principal planes.  This file proves that its common mixed Ricci source has
four distinct real eigenvalues.
-/

namespace RainichKaluza

open scoped Matrix

/-- The active point mixed Ricci source is the explicit two-by-two rank-one
perturbation of the protected Maxwell roots. -/
theorem activeAmbiguityRicciSource_eq_explicit :
    activeAmbiguityRicciSource =
      !![-(3 / 2 : ℝ), 0, -1, 0;
          0, -1, 0, 0;
          1, 0, 3, 0;
          0, 0, 0, 1] := by
  rw [activeAmbiguityRicciSource,
    activeAmbiguityMaxwellStress_eq_canonicalResidual]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedCanonicalScalarRicciSource,
      activeAmbiguityScalarCovector, canonicalMaxwellResidual,
      minkowskiMetric, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The principal-plane permutation placing the mixed scalar block first. -/
noncomputable def genericActiveAmbiguityBlockEquiv :
    Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  { toFun := fun i =>
      if i = 0 then Sum.inl 0
      else if i = 2 then Sum.inl 1
      else if i = 1 then Sum.inr 0
      else Sum.inr 1
    invFun := fun s => match s with
      | Sum.inl i => if i = 0 then 0 else 2
      | Sum.inr i => if i = 0 then 1 else 3
    left_inv := by
      intro i
      fin_cases i <;> simp
    right_inv := by
      intro s
      rcases s with i | i <;> fin_cases i <;> simp }

/-- The complementary mixed scalar block. -/
noncomputable def genericActiveAmbiguityScalarBlock :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(3 / 2 : ℝ), -1;
      1, 3]

/-- The two protected Maxwell roots. -/
def genericActiveAmbiguityProtectedBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, 0;
      0, 1]

/-- Reindexing exposes the exact scalar/protected block decomposition. -/
theorem genericActiveAmbiguityRicciSource_reindex :
    Matrix.reindex genericActiveAmbiguityBlockEquiv
        genericActiveAmbiguityBlockEquiv
        activeAmbiguityRicciSource =
      Matrix.fromBlocks genericActiveAmbiguityScalarBlock 0 0
        genericActiveAmbiguityProtectedBlock := by
  rw [activeAmbiguityRicciSource_eq_explicit]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.reindex, genericActiveAmbiguityBlockEquiv,
        genericActiveAmbiguityScalarBlock,
        genericActiveAmbiguityProtectedBlock, Matrix.fromBlocks,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three]

set_option maxHeartbeats 1000000 in
/-- Exact characteristic factorization of the generic active Ricci source. -/
theorem genericActiveAmbiguityRicciSource_charpoly_eval (z : ℝ) :
    Polynomial.eval z activeAmbiguityRicciSource.charpoly =
      (z ^ 2 - 1) * (z ^ 2 - (3 / 2 : ℝ) * z - 7 / 2) := by
  rw [← Matrix.charpoly_reindex genericActiveAmbiguityBlockEquiv
      activeAmbiguityRicciSource,
    genericActiveAmbiguityRicciSource_reindex,
    Matrix.charpoly_fromBlocks_zero₁₂, Polynomial.eval_mul,
    Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  norm_num [genericActiveAmbiguityScalarBlock,
    genericActiveAmbiguityProtectedBlock, Matrix.trace,
    Matrix.det_fin_two, Fin.sum_univ_succ]
  ring

/-- Lower eigenvalue of the mixed scalar two-plane. -/
noncomputable def activeAmbiguityScalarEigenvalueMinus : ℝ :=
  (3 - Real.sqrt 65) / 4

/-- Upper eigenvalue of the mixed scalar two-plane. -/
noncomputable def activeAmbiguityScalarEigenvaluePlus : ℝ :=
  (3 + Real.sqrt 65) / 4

/-- Both displayed scalar eigenvalues obey the complementary quadratic. -/
theorem activeAmbiguityScalarEigenvalues_quadratic :
    activeAmbiguityScalarEigenvalueMinus ^ 2 -
          (3 / 2 : ℝ) * activeAmbiguityScalarEigenvalueMinus - 7 / 2 = 0 ∧
      activeAmbiguityScalarEigenvaluePlus ^ 2 -
          (3 / 2 : ℝ) * activeAmbiguityScalarEigenvaluePlus - 7 / 2 = 0 := by
  have hsqrt : (Real.sqrt 65) ^ 2 = (65 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  constructor <;>
    simp only [activeAmbiguityScalarEigenvalueMinus,
      activeAmbiguityScalarEigenvaluePlus] <;>
    nlinarith

/-- Exact complete splitting of the point Ricci characteristic polynomial
over the reals. -/
theorem activeAmbiguityRicciSource_charpoly_four_linear_factors (z : ℝ) :
    Polynomial.eval z activeAmbiguityRicciSource.charpoly =
      (z + 1) * (z - 1) *
        (z - activeAmbiguityScalarEigenvalueMinus) *
        (z - activeAmbiguityScalarEigenvaluePlus) := by
  rw [genericActiveAmbiguityRicciSource_charpoly_eval]
  have hsqrt : (Real.sqrt 65) ^ 2 = (65 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  simp only [activeAmbiguityScalarEigenvalueMinus,
    activeAmbiguityScalarEigenvaluePlus]
  nlinarith

/-- The four real characteristic roots are pairwise distinct. -/
theorem activeAmbiguityRicciSource_four_roots_pairwise_distinct :
    (-1 : ℝ) ≠ 1 ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      activeAmbiguityScalarEigenvalueMinus ≠
        activeAmbiguityScalarEigenvaluePlus := by
  have hminus := activeAmbiguityScalarEigenvalues_quadratic.1
  have hplus := activeAmbiguityScalarEigenvalues_quadratic.2
  have hsqrtPos : 0 < Real.sqrt 65 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · norm_num
  constructor
  · intro h
    rw [← h] at hminus
    norm_num at hminus
  constructor
  · intro h
    rw [← h] at hplus
    norm_num at hplus
  constructor
  · intro h
    rw [← h] at hminus
    norm_num at hminus
  constructor
  · intro h
    rw [← h] at hplus
    norm_num at hplus
  · intro h
    simp only [activeAmbiguityScalarEigenvalueMinus,
      activeAmbiguityScalarEigenvaluePlus] at h
    nlinarith

/-- Explicit scalar-plane eigenvector at a root of the complementary
quadratic. -/
noncomputable def activeAmbiguityScalarEigenvector
    (lambda : ℝ) : Fin 4 → ℝ :=
  ![1, 0, -(3 / 2 : ℝ) - lambda, 0]

/-- Every complementary quadratic root gives the displayed eigenpair. -/
theorem activeAmbiguityRicciSource_scalarEigenvector
    (lambda : ℝ)
    (hlambda : lambda ^ 2 - (3 / 2 : ℝ) * lambda - 7 / 2 = 0) :
    activeAmbiguityRicciSource.mulVec
        (activeAmbiguityScalarEigenvector lambda) =
      lambda • activeAmbiguityScalarEigenvector lambda := by
  rw [activeAmbiguityRicciSource_eq_explicit]
  funext i
  fin_cases i
  all_goals norm_num [Matrix.mulVec, dotProduct,
    activeAmbiguityScalarEigenvector, Fin.sum_univ_succ]
  all_goals nlinarith

/-- The two protected Maxwell eigenpairs remain visible in the full Ricci
source. -/
theorem activeAmbiguityRicciSource_protectedEigenpairs :
    activeAmbiguityRicciSource.mulVec ![0, 1, 0, 0] =
        (-1 : ℝ) • ![0, 1, 0, 0] ∧
      activeAmbiguityRicciSource.mulVec ![0, 0, 0, 1] =
        (1 : ℝ) • ![0, 0, 0, 1] := by
  rw [activeAmbiguityRicciSource_eq_explicit]
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **Simple-spectrum certificate.**  The common point Ricci source has four
pairwise-distinct real eigenvalues, with explicit nonzero eigenvectors. -/
theorem activeAmbiguityRicciSource_has_four_distinct_real_eigenpairs :
    (-1 : ℝ) ≠ 1 ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      activeAmbiguityScalarEigenvalueMinus ≠
        activeAmbiguityScalarEigenvaluePlus ∧
      (![0, 1, 0, 0] : Fin 4 → ℝ) ≠ 0 ∧
      (![0, 0, 0, 1] : Fin 4 → ℝ) ≠ 0 ∧
      activeAmbiguityScalarEigenvector
          activeAmbiguityScalarEigenvalueMinus ≠ 0 ∧
      activeAmbiguityScalarEigenvector
          activeAmbiguityScalarEigenvaluePlus ≠ 0 ∧
      activeAmbiguityRicciSource.mulVec ![0, 1, 0, 0] =
        (-1 : ℝ) • ![0, 1, 0, 0] ∧
      activeAmbiguityRicciSource.mulVec ![0, 0, 0, 1] =
        (1 : ℝ) • ![0, 0, 0, 1] ∧
      activeAmbiguityRicciSource.mulVec
          (activeAmbiguityScalarEigenvector
            activeAmbiguityScalarEigenvalueMinus) =
        activeAmbiguityScalarEigenvalueMinus •
          activeAmbiguityScalarEigenvector
            activeAmbiguityScalarEigenvalueMinus ∧
      activeAmbiguityRicciSource.mulVec
          (activeAmbiguityScalarEigenvector
            activeAmbiguityScalarEigenvaluePlus) =
        activeAmbiguityScalarEigenvaluePlus •
          activeAmbiguityScalarEigenvector
            activeAmbiguityScalarEigenvaluePlus := by
  rcases activeAmbiguityRicciSource_four_roots_pairwise_distinct with
    ⟨hne, hmminus, hmplus, hpminus, hpplus, hmmp⟩
  refine ⟨hne, hmminus, hmplus, hpminus, hpplus, hmmp, ?_, ?_, ?_, ?_,
    activeAmbiguityRicciSource_protectedEigenpairs.1,
    activeAmbiguityRicciSource_protectedEigenpairs.2,
    activeAmbiguityRicciSource_scalarEigenvector _
      activeAmbiguityScalarEigenvalues_quadratic.1,
    activeAmbiguityRicciSource_scalarEigenvector _
      activeAmbiguityScalarEigenvalues_quadratic.2⟩
  · intro h
    have hcomponent : (1 : ℝ) = 0 := by simpa using congrFun h 1
    norm_num at hcomponent
  · intro h
    have hcomponent : (1 : ℝ) = 0 := by simpa using congrFun h 3
    norm_num at hcomponent
  · intro h
    have hcomponent : (1 : ℝ) = 0 := by
      simpa [activeAmbiguityScalarEigenvector] using congrFun h 0
    norm_num at hcomponent
  · intro h
    have hcomponent : (1 : ℝ) = 0 := by
      simpa [activeAmbiguityScalarEigenvector] using congrFun h 0
    norm_num at hcomponent

/-- **Simple-spectrum Ricci/exterior bridge for the active continuum.**
For every coupling, this conjoins the common point Ricci value and first jet,
physical activity, exterior closure, and the six simple-spectrum inequalities.
The larger Hodge/scalar/channel package is stated separately by
`activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling`. -/
theorem activeAmbiguity_simpleSpectrum_commonFormalMetricThreeJet_for_every_coupling
    (a : ℝ) :
    ((-1 : ℝ) ≠ 1 ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      activeAmbiguityScalarEigenvalueMinus ≠
        activeAmbiguityScalarEigenvaluePlus) ∧
      IsCoordinateMaxwellStressActiveWedge
        (matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField)
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet a)
        activeAmbiguityScalarCovector ∧
      (∀ n p,
        normalFrameBaseRicci minkowskiSign
            activeAmbiguityFormalMetricJet2 n p =
          activeAmbiguityCovariantRicciSource n p) ∧
      (∀ r n p,
        coordinateRicciFirstJet minkowskiMetric 0
            activeAmbiguityFormalMetricJet2
            activeAmbiguityFormalMetricJet3 r n p =
          (minkowskiMetric * activeAmbiguityRicciSourceFirstJet a r) n p) ∧
      EMDExteriorClosure matrixOneWedgeTwo activeAmbiguityScalarCovector a
        activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge
        (matrixExteriorDerivative (activeAmbiguityMaxwellFirstJet a))
        (matrixExteriorDerivative
          (activeAmbiguityMaxwellHodgeFirstJet a)) := by
  have hsimple := activeAmbiguityRicciSource_four_roots_pairwise_distinct
  have hformal :=
    activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling a
  exact ⟨hsimple, hformal.1, hformal.2.2.2.1,
    hformal.2.2.2.2.1, hformal.2.2.2.2.2.2.2.1⟩

/-- At the simple-spectrum point, the Kaluza value and the non-Kaluza
control retain the complete active formal metric-three-jet collision. -/
theorem exists_simpleSpectrum_activeCommonFormalMetricThreeJet_kaluza_vs_one :
    ((-1 : ℝ) ≠ 1 ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      activeAmbiguityScalarEigenvalueMinus ≠
        activeAmbiguityScalarEigenvaluePlus) ∧
      ((Real.sqrt 3) ^ 2 ≠ (1 : ℝ) ^ 2 ∧
        activeAmbiguityMaxwellFirstJet (Real.sqrt 3) ≠
          activeAmbiguityMaxwellFirstJet 1 ∧
        CovectorWedgeActive
          (activeAmbiguityPhysicalComplexionFromDoubleAngleJet
            (Real.sqrt 3))
          (canonicalPrincipalReflectionCovector
            activeAmbiguityScalarCovector) ∧
        CovectorWedgeActive
          (activeAmbiguityPhysicalComplexionFromDoubleAngleJet 1)
          (canonicalPrincipalReflectionCovector
            activeAmbiguityScalarCovector) ∧
        (∀ r s i j,
          activeAmbiguityFormalMetricJet2 r s i j =
              activeAmbiguityFormalMetricJet2 s r i j ∧
            activeAmbiguityFormalMetricJet2 r s i j =
              activeAmbiguityFormalMetricJet2 r s j i) ∧
        (∀ r s t i j,
          activeAmbiguityFormalMetricJet3 r s t i j =
              activeAmbiguityFormalMetricJet3 s r t i j ∧
            activeAmbiguityFormalMetricJet3 r s t i j =
              activeAmbiguityFormalMetricJet3 r t s i j ∧
            activeAmbiguityFormalMetricJet3 r s t i j =
              activeAmbiguityFormalMetricJet3 r s t j i) ∧
        (∀ n p,
          normalFrameBaseRicci minkowskiSign
              activeAmbiguityFormalMetricJet2 n p =
            activeAmbiguityCovariantRicciSource n p) ∧
        (∀ a ∈ ({Real.sqrt 3, 1} : Set ℝ), ∀ r n p,
          coordinateRicciFirstJet minkowskiMetric 0
              activeAmbiguityFormalMetricJet2
              activeAmbiguityFormalMetricJet3 r n p =
            (minkowskiMetric *
              activeAmbiguityRicciSourceFirstJet a r) n p) ∧
        coordinateMetricHodgeTwoForm4 minkowskiMetric
            activeAmbiguityMaxwellField = activeAmbiguityMaxwellHodge ∧
        (∀ a ∈ ({Real.sqrt 3, 1} : Set ℝ), ∀ k,
          coordinateMetricHodgeTwoForm4 minkowskiMetric
              (activeAmbiguityMaxwellFirstJet a k) =
            activeAmbiguityMaxwellHodgeFirstJet a k) ∧
        EMDExteriorClosure matrixOneWedgeTwo activeAmbiguityScalarCovector
          (Real.sqrt 3) activeAmbiguityMaxwellField
          activeAmbiguityMaxwellHodge
          (matrixExteriorDerivative
            (activeAmbiguityMaxwellFirstJet (Real.sqrt 3)))
          (matrixExteriorDerivative
            (activeAmbiguityMaxwellHodgeFirstJet (Real.sqrt 3))) ∧
        EMDExteriorClosure matrixOneWedgeTwo activeAmbiguityScalarCovector
          1 activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge
          (matrixExteriorDerivative (activeAmbiguityMaxwellFirstJet 1))
          (matrixExteriorDerivative
            (activeAmbiguityMaxwellHodgeFirstJet 1)) ∧
        genericEMDScalarJetResidual (Real.sqrt 3) 0
            activeAmbiguityMaxwellField = 0 ∧
        genericEMDScalarJetResidual 1 0
            activeAmbiguityMaxwellField = 0) := by
  exact ⟨activeAmbiguityRicciSource_four_roots_pairwise_distinct,
    exists_activeCommonFormalMetricThreeJet_kaluza_vs_one⟩

end RainichKaluza
