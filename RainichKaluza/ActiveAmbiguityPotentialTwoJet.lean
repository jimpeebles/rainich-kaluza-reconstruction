import RainichKaluza.ThirdOrderMatterJetAmbiguity
import RainichKaluza.PhysicalMaxwellFieldRealization
import RainichKaluza.RadialGaugePotentialTwoJet

/-!
# Physical Maxwell potential two-jet for the active ambiguity family

The active ambiguity is written using the curvature-normalized rescaled
Maxwell form

`H = exp (a * phi / 2) F / sqrt 2`.

At the marked point `phi = 0`, unweighting therefore leaves the point value
of `H` unchanged and changes its first jet by the product-rule term
`-(a / 2) dphi ⊗ H`.  The first rescaled EMD exterior equation proves that
this unweighted first jet is closed.  Multiplication by `sqrt 2` then returns
the convention registry's physical Maxwell field `F`.

This file makes that finite-jet handoff explicit for the active family and
feeds it to `radialGaugePotentialTwoJet4_realizes`.  It is a finite point-jet
statement, not an all-order field realization.
-/

namespace RainichKaluza

open scoped Matrix

/-- At `phi = 0`, the exponentially unweighted curvature-normalized field is
the convention-normalized physical field `F / sqrt 2`. -/
def activeAmbiguityUnweightedNormalizedMaxwellField : Matrix4 :=
  activeAmbiguityMaxwellField

/-- Product-rule first jet of `F / sqrt 2` obtained by unweighting the active
rescaled Maxwell jet at `phi = 0`. -/
noncomputable def activeAmbiguityUnweightedNormalizedMaxwellFirstJet
    (a : ℝ) : TwoFormFirstDerivative4 :=
  scaledTwoFormFirstJet 1
    (negativeEMDWeightDerivative a 1 activeAmbiguityScalarCovector)
    activeAmbiguityMaxwellField
    (activeAmbiguityMaxwellFirstJet a)

/-- The active rescaled point field is alternating. -/
theorem activeAmbiguityMaxwellField_transpose :
    activeAmbiguityMaxwellFieldᵀ = -activeAmbiguityMaxwellField := by
  simpa only [activeAmbiguityMaxwellField] using
    canonicalMaxwellTwoForm_transpose 1 1

/-- Every directional matrix in the common active perturbation is
alternating. -/
theorem activeAmbiguityCommonMaxwellFirstJet_transpose
    (k : Fin 4) :
    (activeAmbiguityCommonMaxwellFirstJet k)ᵀ =
      -activeAmbiguityCommonMaxwellFirstJet k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [activeAmbiguityCommonMaxwellFirstJet]

/-- The active rescaled Maxwell first jet is alternating in its two-form
slots for every coupling. -/
theorem activeAmbiguityMaxwellFirstJet_transpose
    (a : ℝ) (k : Fin 4) :
    (activeAmbiguityMaxwellFirstJet a k)ᵀ =
      -activeAmbiguityMaxwellFirstJet a k := by
  rw [activeAmbiguityMaxwellFirstJet, Matrix.transpose_add,
    Matrix.transpose_smul,
    activeAmbiguityCommonMaxwellFirstJet_transpose,
    show activeAmbiguityMaxwellHodgeᵀ =
        -activeAmbiguityMaxwellHodge by
      simpa only [activeAmbiguityMaxwellHodge] using
        canonicalMaxwellTwoForm_transpose (-1) 1]
  module

/-- The product-rule unweighted first jet remains alternating. -/
theorem activeAmbiguityUnweightedNormalizedMaxwellFirstJet_transpose
    (a : ℝ) (k : Fin 4) :
    (activeAmbiguityUnweightedNormalizedMaxwellFirstJet a k)ᵀ =
      -activeAmbiguityUnweightedNormalizedMaxwellFirstJet a k := by
  rw [activeAmbiguityUnweightedNormalizedMaxwellFirstJet,
    scaledTwoFormFirstJet, Matrix.transpose_add,
    Matrix.transpose_smul, Matrix.transpose_smul,
    activeAmbiguityMaxwellField_transpose,
    activeAmbiguityMaxwellFirstJet_transpose]
  module

/-- Unweighting cancels the rescaled Bianchi source exactly, so the complete
unweighted coordinate first jet is closed. -/
theorem matrixExteriorDerivative_activeAmbiguityUnweightedNormalizedMaxwellFirstJet
    (a : ℝ) :
    matrixExteriorDerivative
        (activeAmbiguityUnweightedNormalizedMaxwellFirstJet a) = 0 := by
  rw [activeAmbiguityUnweightedNormalizedMaxwellFirstJet,
    matrixExteriorDerivative_scaledTwoFormFirstJet]
  apply closed_unscaledMaxwell_of_rescaled_bianchi
      matrixOneWedgeTwo activeAmbiguityScalarCovector
      (negativeEMDWeightDerivative a 1 activeAmbiguityScalarCovector)
      activeAmbiguityMaxwellField
      (matrixExteriorDerivative (activeAmbiguityMaxwellFirstJet a)) a 1
  · simp [negativeEMDWeightDerivative]
  · exact matrixExteriorDerivative_activeAmbiguityMaxwellFirstJet a

/-- Convention-registry physical Maxwell value `F`, obtained from the
curvature-normalized unweighted value `F / sqrt 2`. -/
noncomputable def activeAmbiguityPhysicalMaxwellField : Matrix4 :=
  Real.sqrt 2 • activeAmbiguityUnweightedNormalizedMaxwellField

/-- Convention-registry physical Maxwell first jet. -/
noncomputable def activeAmbiguityPhysicalMaxwellFirstJet
    (a : ℝ) : TwoFormFirstDerivative4 :=
  fun k => Real.sqrt 2 •
    activeAmbiguityUnweightedNormalizedMaxwellFirstJet a k

/-- The physical point field is alternating. -/
theorem activeAmbiguityPhysicalMaxwellField_transpose :
    activeAmbiguityPhysicalMaxwellFieldᵀ =
      -activeAmbiguityPhysicalMaxwellField := by
  rw [activeAmbiguityPhysicalMaxwellField, Matrix.transpose_smul,
    activeAmbiguityUnweightedNormalizedMaxwellField,
    activeAmbiguityMaxwellField_transpose]
  simp

/-- The complete physical Maxwell first jet is alternating. -/
theorem activeAmbiguityPhysicalMaxwellFirstJet_transpose
    (a : ℝ) (k : Fin 4) :
    (activeAmbiguityPhysicalMaxwellFirstJet a k)ᵀ =
      -activeAmbiguityPhysicalMaxwellFirstJet a k := by
  rw [activeAmbiguityPhysicalMaxwellFirstJet, Matrix.transpose_smul,
    activeAmbiguityUnweightedNormalizedMaxwellFirstJet_transpose]
  simp

/-- Constant normalization preserves closure of the complete physical
Maxwell first jet. -/
theorem matrixExteriorDerivative_activeAmbiguityPhysicalMaxwellFirstJet
    (a : ℝ) :
    matrixExteriorDerivative (activeAmbiguityPhysicalMaxwellFirstJet a) = 0 := by
  ext k i j
  have hclosed :
      activeAmbiguityUnweightedNormalizedMaxwellFirstJet a k i j +
          activeAmbiguityUnweightedNormalizedMaxwellFirstJet a i j k +
          activeAmbiguityUnweightedNormalizedMaxwellFirstJet a j k i = 0 := by
    simpa [matrixExteriorDerivative] using congrArg
      (fun D : ThreeTensor4 => D k i j)
      (matrixExteriorDerivative_activeAmbiguityUnweightedNormalizedMaxwellFirstJet a)
  change Real.sqrt 2 *
          activeAmbiguityUnweightedNormalizedMaxwellFirstJet a k i j +
        Real.sqrt 2 *
          activeAmbiguityUnweightedNormalizedMaxwellFirstJet a i j k +
        Real.sqrt 2 *
          activeAmbiguityUnweightedNormalizedMaxwellFirstJet a j k i = 0
  calc
    _ = Real.sqrt 2 *
        (activeAmbiguityUnweightedNormalizedMaxwellFirstJet a k i j +
          activeAmbiguityUnweightedNormalizedMaxwellFirstJet a i j k +
          activeAmbiguityUnweightedNormalizedMaxwellFirstJet a j k i) := by ring
    _ = Real.sqrt 2 * 0 := by rw [hclosed]
    _ = 0 := by ring

/-- One explicit physical-jet component records the coupling with the
convention-registry normalization. -/
theorem activeAmbiguityPhysicalMaxwellFirstJet_component
    (a : ℝ) :
    activeAmbiguityPhysicalMaxwellFirstJet a 0 0 1 =
      -(Real.sqrt 2 * a) := by
  rw [activeAmbiguityPhysicalMaxwellFirstJet,
    activeAmbiguityUnweightedNormalizedMaxwellFirstJet,
    scaledTwoFormFirstJet, negativeEMDWeightDerivative]
  simp [activeAmbiguityScalarCovector, activeAmbiguityMaxwellField,
    activeAmbiguityMaxwellFirstJet, activeAmbiguityCommonMaxwellFirstJet,
    activeAmbiguityMaxwellHodge, activeAmbiguityShearComplexionOneForm,
    canonicalMaxwellTwoForm, canonicalPrincipalReflectionCovector]
  ring

/-- The correctly unweighted physical Maxwell first jet remains injective in
the coupling parameter. -/
theorem activeAmbiguityPhysicalMaxwellFirstJet_injective :
    Function.Injective activeAmbiguityPhysicalMaxwellFirstJet := by
  intro a b hab
  have hcomponent := congrFun (congrFun (congrFun hab 0) 0) 1
  rw [activeAmbiguityPhysicalMaxwellFirstJet_component,
    activeAmbiguityPhysicalMaxwellFirstJet_component] at hcomponent
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  exact (mul_left_cancel₀ hsqrt) (by linarith)

/-- First radial-gauge potential jet for the physical Maxwell value. -/
noncomputable def activeAmbiguityPhysicalRadialPotentialFirstJet : Matrix4 :=
  radialGaugePotentialFirstJet4 activeAmbiguityPhysicalMaxwellField

/-- Second radial-gauge potential jet for the coupling-dependent physical
Maxwell first jet. -/
noncomputable def activeAmbiguityPhysicalRadialPotentialSecondJet
    (a : ℝ) : OneFormSecondDerivative4 :=
  radialGaugePotentialSecondJet4
    (activeAmbiguityPhysicalMaxwellFirstJet a)

/-- **Active-family physical potential two-jet.** For every coupling, the
explicit radial-gauge potential jets have commuting derivative slots and
their curl value and curl first derivative are exactly the convention-
registry physical Maxwell value and first jet. -/
theorem activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes
    (a : ℝ) :
    (∀ i j,
      activeAmbiguityPhysicalRadialPotentialFirstJet i j -
          activeAmbiguityPhysicalRadialPotentialFirstJet j i =
        activeAmbiguityPhysicalMaxwellField i j) ∧
    (∀ k i j,
      activeAmbiguityPhysicalRadialPotentialSecondJet a k i j =
        activeAmbiguityPhysicalRadialPotentialSecondJet a i k j) ∧
    (∀ k i j,
      activeAmbiguityPhysicalRadialPotentialSecondJet a k i j -
          activeAmbiguityPhysicalRadialPotentialSecondJet a k j i =
        activeAmbiguityPhysicalMaxwellFirstJet a k i j) := by
  exact radialGaugePotentialTwoJet4_realizes
    activeAmbiguityPhysicalMaxwellField
    (activeAmbiguityPhysicalMaxwellFirstJet a)
    activeAmbiguityPhysicalMaxwellField_transpose
    (activeAmbiguityPhysicalMaxwellFirstJet_transpose a)
    (matrixExteriorDerivative_activeAmbiguityPhysicalMaxwellFirstJet a)

end RainichKaluza
