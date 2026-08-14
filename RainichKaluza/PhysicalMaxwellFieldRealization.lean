import RainichKaluza.CurvatureKaluzaComposition
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

set_option maxSynthPendingDepth 2

/-!
# Field-level realization of the unweighted Maxwell seed

The Phase-III obstruction theorem is expressed using matrix-valued two-form
jets, whereas radial potential recovery expects an actual `C¹` field of
continuous bilinear forms.  This file supplies the exact finite-dimensional
conversion between those two representations and proves that the conversion
commutes with first jets and coordinate exterior differentiation.

The final constructions unweight a differentiable rescaled Maxwell field by
`exp(-a phi/2)` and positively weight its rescaled Hodge partner by
`exp(a phi/2)`. Their Frechet derivatives are the genuine product-rule
derivatives, and the two already-proved exponential-weight exterior jets make
the physical two-form and weighted dual flux closed in the full
`IsC1ClosedTwoFormOn` sense.

Normalization note (2026-08-12): the upstream canonical seed has amplitude
`sqrt(2q)` and its ordinary Maxwell stress equals the Ricci residual. It is
therefore `H=exp(a phi/2)F/sqrt(2)` in the convention registry. The legacy
`physical*` definitions below unweight `H` and hence represent `F/sqrt(2)`.
Their closure theorems are unchanged, but the eventual EMD/uplift matching
interface must multiply them by the constant `sqrt(2)`.  The
`conventionNormalizedPhysicalMaxwell*` bridge near the end of this file now
performs that scaling while preserving the complete closed `C¹` package and
its gauge potentials.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

/-- A coordinate matrix as a continuous bilinear form on four-space. -/
noncomputable def matrixContinuousBilinForm4
    (F : Matrix4) : ContinuousBilinForm BaseCoordinateSpace :=
  (Matrix.toBilin' F).toContinuousBilinearMap

/-- The coordinate directions are Mathlib's standard basis vectors. -/
theorem coordinateDirection_eq_single (i : Fin 4) :
    coordinateDirection i = Pi.single i 1 := by
  ext j
  simp [coordinateDirection, Pi.single_apply, eq_comm]

@[simp]
theorem oneForm4ContinuousLinearMap_coordinateDirection
    (v : OneForm4) (i : Fin 4) :
    oneForm4ContinuousLinearMap v (coordinateDirection i) = v i := by
  simp [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    coordinateDirection, eq_comm]

@[simp]
theorem matrixContinuousBilinForm4_apply
    (F : Matrix4) (u v : BaseCoordinateSpace) :
    matrixContinuousBilinForm4 F u v =
      ∑ i, ∑ j, u i * F i j * v j := by
  exact Matrix.toBilin'_apply F u v

@[simp]
theorem matrixContinuousBilinForm4_coordinateDirection
    (F : Matrix4) (i j : Fin 4) :
    matrixContinuousBilinForm4 F (coordinateDirection i)
      (coordinateDirection j) = F i j := by
  simpa only [coordinateDirection_eq_single, matrixContinuousBilinForm4,
    LinearMap.toContinuousBilinearMap_apply] using
    Matrix.toBilin'_single F i j

/-- Matrix-to-bilinear-form conversion as an algebraic linear map. -/
noncomputable def matrixContinuousBilinForm4Linear :
    Matrix4 →ₗ[ℝ] ContinuousBilinForm BaseCoordinateSpace where
  toFun := matrixContinuousBilinForm4
  map_add' := by
    intro F G
    ext u v
    change Matrix.toBilin' (F + G) u v =
      Matrix.toBilin' F u v + Matrix.toBilin' G u v
    rw [map_add]
    rfl
  map_smul' := by
    intro c F
    ext u v
    change Matrix.toBilin' (c • F) u v = c • Matrix.toBilin' F u v
    rw [map_smul]
    rfl

/-- The same conversion as a continuous linear map. -/
noncomputable def matrixContinuousBilinForm4CLM :
    Matrix4 →L[ℝ] ContinuousBilinForm BaseCoordinateSpace :=
  { toLinearMap := matrixContinuousBilinForm4Linear
    cont := by
      exact LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := Matrix4)
        (F' := ContinuousBilinForm BaseCoordinateSpace)
        matrixContinuousBilinForm4Linear }

@[simp]
theorem matrixContinuousBilinForm4CLM_apply
    (F : Matrix4) :
    matrixContinuousBilinForm4CLM F = matrixContinuousBilinForm4 F := by
  rfl

@[simp]
theorem matrixContinuousBilinForm4_smul
    (r : ℝ) (F : Matrix4) :
    matrixContinuousBilinForm4 (r • F) =
      r • matrixContinuousBilinForm4 F := by
  change matrixContinuousBilinForm4Linear (r • F) =
    r • matrixContinuousBilinForm4Linear F
  exact map_smul matrixContinuousBilinForm4Linear r F

/-- Directional evaluation of a coordinate matrix first jet. -/
def matrixFirstJetEvaluate
    (D : Fin 4 → Matrix4) (u : BaseCoordinateSpace) : Matrix4 :=
  fun i j => ∑ k, u k * D k i j

/-- Directional evaluation is linear in the direction. -/
def matrixFirstJetLinear (D : Fin 4 → Matrix4) :
    BaseCoordinateSpace →ₗ[ℝ] Matrix4 where
  toFun := matrixFirstJetEvaluate D
  map_add' := by
    intro u v
    ext i j
    simp only [matrixFirstJetEvaluate, Pi.add_apply, add_mul,
      Finset.sum_add_distrib, Matrix.add_apply]
  map_smul' := by
    intro c u
    ext i j
    simp only [matrixFirstJetEvaluate, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Matrix.smul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Continuous directional evaluation of a coordinate matrix first jet. -/
noncomputable def matrixFirstJetCLM (D : Fin 4 → Matrix4) :
    BaseCoordinateSpace →L[ℝ] Matrix4 :=
  LinearMap.toContinuousLinearMap (matrixFirstJetLinear D)

@[simp]
theorem matrixFirstJetCLM_apply
    (D : Fin 4 → Matrix4) (u : BaseCoordinateSpace) :
    matrixFirstJetCLM D u = matrixFirstJetEvaluate D u := rfl

@[simp]
theorem matrixFirstJetCLM_coordinateDirection
    (D : Fin 4 → Matrix4) (k : Fin 4) :
    matrixFirstJetCLM D (coordinateDirection k) = D k := by
  ext i j
  simp [matrixFirstJetCLM, matrixFirstJetLinear, matrixFirstJetEvaluate,
    coordinateDirection]

/-- A matrix first jet as the continuous-linear derivative of a continuous
bilinear-form field. -/
noncomputable def matrixFirstJetBilinFDeriv
    (D : Fin 4 → Matrix4) :
    BaseCoordinateSpace →L[ℝ] ContinuousBilinForm BaseCoordinateSpace :=
  matrixContinuousBilinForm4CLM.comp (matrixFirstJetCLM D)

@[simp]
theorem matrixFirstJetBilinFDeriv_apply
    (D : Fin 4 → Matrix4) (u v w : BaseCoordinateSpace) :
    matrixFirstJetBilinFDeriv D u v w =
      ∑ i, ∑ j, (∑ k, u k * D k i j) * v i * w j := by
  simp only [matrixFirstJetBilinFDeriv, ContinuousLinearMap.comp_apply,
    matrixContinuousBilinForm4CLM_apply,
    matrixContinuousBilinForm4_apply, matrixFirstJetCLM_apply,
    matrixFirstJetEvaluate]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp]
theorem matrixFirstJetBilinFDeriv_coordinateDirection
    (D : Fin 4 → Matrix4) (k i j : Fin 4) :
    matrixFirstJetBilinFDeriv D (coordinateDirection k)
      (coordinateDirection i) (coordinateDirection j) = D k i j := by
  rw [matrixFirstJetBilinFDeriv, ContinuousLinearMap.comp_apply,
    matrixFirstJetCLM_coordinateDirection]
  exact matrixContinuousBilinForm4_coordinateDirection (D k) i j

/-- The continuous-linear Frechet derivative representation remembers every
coordinate component of the matrix first jet. -/
theorem matrixFirstJetBilinFDeriv_injective :
    Function.Injective matrixFirstJetBilinFDeriv := by
  intro D D' h
  funext k
  ext i j
  have hcomponent := congrArg
    (fun A : BaseCoordinateSpace →L[ℝ]
        ContinuousBilinForm BaseCoordinateSpace =>
      A (coordinateDirection k) (coordinateDirection i)
        (coordinateDirection j)) h
  simpa only [matrixFirstJetBilinFDeriv_coordinateDirection] using hcomponent

/-- Product-rule first jet of a scalar-weighted matrix two-form. -/
def scaledTwoFormFirstJet
    (r : ℝ) (dr : OneForm4) (F : Matrix4)
    (dF : Fin 4 → Matrix4) : Fin 4 → Matrix4 :=
  fun k => dr k • F + r • dF k

/-- Exteriorization of the full scaled first jet is exactly the abstract
scaled exterior derivative used at the Phase-III/IV boundary. -/
theorem matrixExteriorDerivative_scaledTwoFormFirstJet
    (r : ℝ) (dr : OneForm4) (F : Matrix4)
    (dF : Fin 4 → Matrix4) :
    matrixExteriorDerivative (scaledTwoFormFirstJet r dr F dF) =
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo r dr F
        (matrixExteriorDerivative dF) := by
  ext k i j
  simp [matrixExteriorDerivative, scaledTwoFormFirstJet,
    scaledTwoFormExteriorDerivative, matrixOneWedgeTwo,
    matrixOneWedgeTwoTensor]
  ring

/-- Cyclic derivative of a coordinate first jet as an algebraic trilinear
form.  Packaging the expression linearly lets the standard coordinate basis
upgrade componentwise exterior closure to arbitrary directions. -/
noncomputable def matrixFirstJetCyclicLinear
    (D : Fin 4 → Matrix4) :
    BaseCoordinateSpace →ₗ[ℝ]
      BaseCoordinateSpace →ₗ[ℝ]
        BaseCoordinateSpace →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := fun b =>
        { toFun := fun c =>
            matrixFirstJetBilinFDeriv D a b c +
              matrixFirstJetBilinFDeriv D b c a +
              matrixFirstJetBilinFDeriv D c a b
          map_add' := by
            intro c d
            simp only [map_add, add_apply]
            ring
          map_smul' := by
            intro r c
            simp only [map_smul, RingHom.id_apply, smul_apply, smul_eq_mul]
            ring }
      map_add' := by
        intro b c
        apply LinearMap.ext
        intro d
        change
          matrixFirstJetBilinFDeriv D a (b + c) d +
                matrixFirstJetBilinFDeriv D (b + c) d a +
                matrixFirstJetBilinFDeriv D d a (b + c) =
            (matrixFirstJetBilinFDeriv D a b d +
                matrixFirstJetBilinFDeriv D b d a +
                matrixFirstJetBilinFDeriv D d a b) +
              (matrixFirstJetBilinFDeriv D a c d +
                matrixFirstJetBilinFDeriv D c d a +
                matrixFirstJetBilinFDeriv D d a c)
        simp only [map_add, add_apply]
        ring
      map_smul' := by
        intro r b
        apply LinearMap.ext
        intro c
        change
          matrixFirstJetBilinFDeriv D a (r • b) c +
                matrixFirstJetBilinFDeriv D (r • b) c a +
                matrixFirstJetBilinFDeriv D c a (r • b) =
            r • (matrixFirstJetBilinFDeriv D a b c +
              matrixFirstJetBilinFDeriv D b c a +
              matrixFirstJetBilinFDeriv D c a b)
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    change
      matrixFirstJetBilinFDeriv D (a + b) c d +
            matrixFirstJetBilinFDeriv D c d (a + b) +
            matrixFirstJetBilinFDeriv D d (a + b) c =
        (matrixFirstJetBilinFDeriv D a c d +
            matrixFirstJetBilinFDeriv D c d a +
            matrixFirstJetBilinFDeriv D d a c) +
          (matrixFirstJetBilinFDeriv D b c d +
            matrixFirstJetBilinFDeriv D c d b +
            matrixFirstJetBilinFDeriv D d b c)
    simp only [map_add, add_apply]
    ring
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    change
      matrixFirstJetBilinFDeriv D (r • a) b c +
            matrixFirstJetBilinFDeriv D b c (r • a) +
            matrixFirstJetBilinFDeriv D c (r • a) b =
        r • (matrixFirstJetBilinFDeriv D a b c +
          matrixFirstJetBilinFDeriv D b c a +
          matrixFirstJetBilinFDeriv D c a b)
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

@[simp]
theorem matrixFirstJetCyclicLinear_apply
    (D : Fin 4 → Matrix4) (a b c : BaseCoordinateSpace) :
    matrixFirstJetCyclicLinear D a b c =
      matrixFirstJetBilinFDeriv D a b c +
        matrixFirstJetBilinFDeriv D b c a +
        matrixFirstJetBilinFDeriv D c a b := rfl

/-- Coordinate exterior closure of a matrix first jet is full exterior
closure of the corresponding continuous-bilinear-form derivative. -/
theorem matrixFirstJetBilinFDeriv_closed_of_exterior_zero
    (D : Fin 4 → Matrix4)
    (hclosed : matrixExteriorDerivative D = 0) :
    ∀ a b c : BaseCoordinateSpace,
      matrixFirstJetBilinFDeriv D a b c +
          matrixFirstJetBilinFDeriv D b c a +
          matrixFirstJetBilinFDeriv D c a b = 0 := by
  have hlinear : matrixFirstJetCyclicLinear D = 0 := by
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro k
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro i
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro j
    rw [Pi.basisFun_apply, Pi.basisFun_apply, Pi.basisFun_apply]
    rw [← coordinateDirection_eq_single k,
      ← coordinateDirection_eq_single i,
      ← coordinateDirection_eq_single j]
    simp only [matrixFirstJetCyclicLinear_apply, LinearMap.zero_apply,
      matrixFirstJetBilinFDeriv_coordinateDirection]
    have hcomponent := congrArg (fun H : ThreeTensor4 => H k i j) hclosed
    simpa only [matrixExteriorDerivative, Pi.zero_apply] using hcomponent
  intro a b c
  have hcomponent := congrArg
    (fun T : BaseCoordinateSpace →ₗ[ℝ]
      BaseCoordinateSpace →ₗ[ℝ]
        BaseCoordinateSpace →ₗ[ℝ] ℝ => T a b c) hlinear
  simpa only [matrixFirstJetCyclicLinear_apply, LinearMap.zero_apply]
    using hcomponent

/-- The directional derivative associated to a scaled coordinate first jet
is exactly the Frechet product-rule derivative. -/
theorem matrixFirstJetCLM_scaledTwoFormFirstJet
    (r : ℝ) (dr : OneForm4) (F : Matrix4)
    (dF : Fin 4 → Matrix4) :
    matrixFirstJetCLM (scaledTwoFormFirstJet r dr F dF) =
      r • matrixFirstJetCLM dF +
        (oneForm4ContinuousLinearMap dr).smulRight F := by
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro k
  rw [Pi.basisFun_apply, ← coordinateDirection_eq_single k]
  change matrixFirstJetCLM (scaledTwoFormFirstJet r dr F dF)
      (coordinateDirection k) =
    (r • matrixFirstJetCLM dF +
      (oneForm4ContinuousLinearMap dr).smulRight F)
        (coordinateDirection k)
  rw [matrixFirstJetCLM_coordinateDirection]
  change scaledTwoFormFirstJet r dr F dF k =
    r • matrixFirstJetCLM dF (coordinateDirection k) +
      (oneForm4ContinuousLinearMap dr) (coordinateDirection k) • F
  rw [matrixFirstJetCLM_coordinateDirection]
  simp only [scaledTwoFormFirstJet,
    oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    coordinateDirection]
  rw [show (∑ x, dr x * if x = k then 1 else 0) = dr k by simp]
  module

/-- Matrix-to-form conversion carries the coordinate product-rule jet to
the ordinary Frechet product rule for scalar multiplication. -/
theorem matrixFirstJetBilinFDeriv_scaledTwoFormFirstJet
    (r : ℝ) (dr : OneForm4) (F : Matrix4)
    (dF : Fin 4 → Matrix4) :
    matrixFirstJetBilinFDeriv
        (scaledTwoFormFirstJet r dr F dF) =
      r • matrixFirstJetBilinFDeriv dF +
        (oneForm4ContinuousLinearMap dr).smulRight
          (matrixContinuousBilinForm4 F) := by
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro k
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro j
  simp only [Pi.basisFun_apply]
  rw [← coordinateDirection_eq_single k,
    ← coordinateDirection_eq_single i,
    ← coordinateDirection_eq_single j]
  change matrixFirstJetBilinFDeriv
      (scaledTwoFormFirstJet r dr F dF) (coordinateDirection k)
        (coordinateDirection i) (coordinateDirection j) =
    (r • matrixFirstJetBilinFDeriv dF +
      (oneForm4ContinuousLinearMap dr).smulRight
        (matrixContinuousBilinForm4 F)) (coordinateDirection k)
          (coordinateDirection i) (coordinateDirection j)
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply,
    matrixFirstJetBilinFDeriv_coordinateDirection,
    matrixContinuousBilinForm4_coordinateDirection,
    oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    coordinateDirection, scaledTwoFormFirstJet, Matrix.add_apply,
    Matrix.smul_apply]
  rw [show (∑ x, dr x * if x = k then 1 else 0) = dr k by simp]
  ring

/-- A skew coordinate matrix defines an alternating continuous bilinear
form in arbitrary directions. -/
theorem matrixContinuousBilinForm4_alternating_of_transpose_eq_neg
    (F : Matrix4) (hF : Fᵀ = -F) (u v : BaseCoordinateSpace) :
    matrixContinuousBilinForm4 F u v =
      -matrixContinuousBilinForm4 F v u := by
  have hforms : matrixContinuousBilinForm4 F =
      -(matrixContinuousBilinForm4 F).flip := by
    apply ContinuousLinearMap.coe_injective
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro j
    simp only [Pi.basisFun_apply]
    rw [← coordinateDirection_eq_single i,
      ← coordinateDirection_eq_single j]
    change matrixContinuousBilinForm4 F (coordinateDirection i)
        (coordinateDirection j) =
      (-(matrixContinuousBilinForm4 F).flip) (coordinateDirection i)
        (coordinateDirection j)
    rw [matrixContinuousBilinForm4_coordinateDirection]
    change F i j =
      -matrixContinuousBilinForm4 F (coordinateDirection j)
        (coordinateDirection i)
    rw [matrixContinuousBilinForm4_coordinateDirection]
    have hcomponent := congrArg (fun M : Matrix4 => M j i) hF
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hcomponent
  have hcomponent := congrArg
    (fun B : ContinuousBilinForm BaseCoordinateSpace => B u v) hforms
  simpa only [neg_apply, ContinuousLinearMap.flip_apply] using hcomponent

/-- Entrywise continuity of coordinate first jets gives continuity of their
continuous-bilinear Frechet derivative fields. -/
theorem continuousOn_matrixFirstJetBilinFDeriv
    {X : Type*} [TopologicalSpace X] {U : Set X}
    (D : X → Fin 4 → Matrix4)
    (hD : ∀ k i j, ContinuousOn (fun z => D z k i j) U) :
    ContinuousOn (fun z => matrixFirstJetBilinFDeriv (D z)) U := by
  rw [continuousOn_clm_apply]
  intro u
  rw [continuousOn_clm_apply]
  intro v
  rw [continuousOn_clm_apply]
  intro w
  simp only [matrixFirstJetBilinFDeriv_apply]
  apply continuousOn_finsetSum Finset.univ
  intro i _
  apply continuousOn_finsetSum Finset.univ
  intro j _
  have hinner : ContinuousOn (fun z => ∑ k, u k * D z k i j) U := by
    apply continuousOn_finsetSum Finset.univ
    intro k _
    exact continuousOn_const.mul (hD k i j)
  exact (hinner.mul continuousOn_const).mul continuousOn_const

/-- A genuine `C¹` rescaled Maxwell field in coordinate-matrix form.  The
first jet is its actual Frechet derivative, not merely a displayed array. -/
structure RescaledMaxwellMatrixC1On (U : Set BaseCoordinateSpace) where
  field : BaseCoordinateSpace → Matrix4
  firstJet : BaseCoordinateSpace → Fin 4 → Matrix4
  differentiable : ∀ z ∈ U,
    HasFDerivAt
      (fun y => matrixContinuousBilinForm4 (field y))
      (matrixFirstJetBilinFDeriv (firstJet z)) z
  firstJet_continuous :
    ∀ k i j, ContinuousOn (fun z => firstJet z k i j) U
  alternating : ∀ z ∈ U, (field z)ᵀ = -field z

namespace RescaledMaxwellMatrixC1On

variable {U : Set BaseCoordinateSpace}

/-- Two genuine `C¹` matrix fields that agree on a neighborhood of a point
have the same stored coordinate first jet there.  This follows from
uniqueness of the Frechet derivative; the stored jet is not independent
auxiliary data. -/
theorem firstJet_eq_of_field_eventuallyEq
    (S T : RescaledMaxwellMatrixC1On U)
    (z : BaseCoordinateSpace) (hz : z ∈ U)
    (hfield : S.field =ᶠ[nhds z] T.field) :
    S.firstJet z = T.firstJet z := by
  have hforms :
      (fun y => matrixContinuousBilinForm4 (S.field y)) =ᶠ[nhds z]
        (fun y => matrixContinuousBilinForm4 (T.field y)) := by
    filter_upwards [hfield] with y hy
    rw [hy]
  have hTForS : HasFDerivAt
      (fun y => matrixContinuousBilinForm4 (S.field y))
      (matrixFirstJetBilinFDeriv (T.firstJet z)) z :=
    (T.differentiable z hz).congr_of_eventuallyEq hforms
  apply matrixFirstJetBilinFDeriv_injective
  exact (S.differentiable z hz).unique hTForS

/-- Exponentially unweighted curvature-normalized Maxwell matrix. Despite the
legacy name, this is `F/sqrt(2)` in the convention-fixed EMD normalization. -/
noncomputable def physicalMatrix
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (z : BaseCoordinateSpace) : Matrix4 :=
  negativeEMDWeight coupling phi z • S.field z

/-- Coordinate first jet of the unweighted physical Maxwell field. -/
noncomputable def physicalFirstJet
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (z : BaseCoordinateSpace) : Fin 4 → Matrix4 :=
  scaledTwoFormFirstJet (negativeEMDWeight coupling phi z)
    (negativeEMDWeightDerivative coupling
      (negativeEMDWeight coupling phi z) (v z))
    (S.field z) (S.firstJet z)

/-- Actual physical Maxwell two-form field in the representation required by
the radial homotopy theorem. -/
noncomputable def physicalField
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (z : BaseCoordinateSpace) :
    ContinuousBilinForm BaseCoordinateSpace :=
  matrixContinuousBilinForm4 (S.physicalMatrix coupling phi z)

/-- Genuine Frechet derivative candidate of the physical Maxwell field. -/
noncomputable def physicalFDeriv
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (z : BaseCoordinateSpace) :
    BaseCoordinateSpace →L[ℝ]
      ContinuousBilinForm BaseCoordinateSpace :=
  matrixFirstJetBilinFDeriv (S.physicalFirstJet coupling phi v z)

/-- Coordinate form of the derivative of the negative EMD weight. -/
theorem oneForm4ContinuousLinearMap_negativeEMDWeightDerivative
    (coupling r : ℝ) (v : OneForm4) :
    oneForm4ContinuousLinearMap
        (negativeEMDWeightDerivative coupling r v) =
      -(((coupling / 2) * r) • oneForm4ContinuousLinearMap v) := by
  rw [negativeEMDWeightDerivative,
    oneForm4ContinuousLinearMap_smul]
  ext u
  simp only [neg_apply, smul_apply, smul_eq_mul]
  ring

/-- The displayed physical first jet is the actual Frechet derivative of the
unweighted continuous-bilinear two-form field. -/
theorem hasFDerivAt_physicalField
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (hphi : ∀ z ∈ U,
      HasFDerivAt phi (oneForm4ContinuousLinearMap (v z)) z)
    {z : BaseCoordinateSpace} (hz : z ∈ U) :
    HasFDerivAt (S.physicalField coupling phi)
      (S.physicalFDeriv coupling phi v z) z := by
  have hweight :
      HasFDerivAt (negativeEMDWeight coupling phi)
        (-(((coupling / 2) * negativeEMDWeight coupling phi z) •
          oneForm4ContinuousLinearMap (v z))) z :=
    hasFDerivAt_negativeEMDWeight coupling (hphi z hz)
  have hproduct :
      HasFDerivAt
        ((negativeEMDWeight coupling phi) •
          (fun y => matrixContinuousBilinForm4 (S.field y)))
        (negativeEMDWeight coupling phi z •
            matrixFirstJetBilinFDeriv (S.firstJet z) +
          (-(((coupling / 2) * negativeEMDWeight coupling phi z) •
            oneForm4ContinuousLinearMap (v z))).smulRight
              (matrixContinuousBilinForm4 (S.field z))) z :=
    hweight.smul (S.differentiable z hz)
  rw [show S.physicalField coupling phi =
      (negativeEMDWeight coupling phi) •
        (fun y => matrixContinuousBilinForm4 (S.field y)) by
    funext y
    change matrixContinuousBilinForm4
      (negativeEMDWeight coupling phi y • S.field y) =
        negativeEMDWeight coupling phi y •
          matrixContinuousBilinForm4 (S.field y)
    exact matrixContinuousBilinForm4_smul _ _]
  change HasFDerivAt
    ((negativeEMDWeight coupling phi) •
      (fun y => matrixContinuousBilinForm4 (S.field y)))
    (matrixFirstJetBilinFDeriv
      (scaledTwoFormFirstJet
        (negativeEMDWeight coupling phi z)
        (negativeEMDWeightDerivative coupling
          (negativeEMDWeight coupling phi z) (v z))
        (S.field z) (S.firstJet z))) z
  rw [matrixFirstJetBilinFDeriv_scaledTwoFormFirstJet]
  simpa only [
    oneForm4ContinuousLinearMap_negativeEMDWeightDerivative] using hproduct

/-- Continuity of the scalar one-form and rescaled first jet makes the full
physical derivative field continuous. -/
theorem continuousOn_physicalFDeriv
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (hphi : ∀ z ∈ U,
      HasFDerivAt phi (oneForm4ContinuousLinearMap (v z)) z)
    (hv : ContinuousOn v U) :
    ContinuousOn (S.physicalFDeriv coupling phi v) U := by
  have hphiContinuous : ContinuousOn phi U :=
    fun z hz => ((hphi z hz).continuousAt).continuousWithinAt
  have hweight : ContinuousOn (negativeEMDWeight coupling phi) U := by
    change ContinuousOn (fun z => Real.exp (-(coupling / 2) * phi z)) U
    have hconstant : ContinuousOn
        (fun _ : BaseCoordinateSpace => -(coupling / 2)) U :=
      continuousOn_const
    exact (hconstant.mul hphiContinuous).rexp
  have hfield : ContinuousOn
      (fun z => matrixContinuousBilinForm4 (S.field z)) U :=
    fun z hz => ((S.differentiable z hz).continuousAt).continuousWithinAt
  have hdr : ContinuousOn
      (fun z => negativeEMDWeightDerivative coupling
        (negativeEMDWeight coupling phi z) (v z)) U := by
    change ContinuousOn (fun z =>
      (-(coupling / 2) * negativeEMDWeight coupling phi z) • v z) U
    exact ((continuousOn_const.mul hweight).smul hv)
  have hphysicalFDeriv : ContinuousOn
      (fun z => matrixFirstJetBilinFDeriv
        (S.physicalFirstJet coupling phi v z)) U := by
    apply continuousOn_matrixFirstJetBilinFDeriv
    intro k i j
    change ContinuousOn (fun z =>
      (negativeEMDWeightDerivative coupling
          (negativeEMDWeight coupling phi z) (v z)) k *
          S.field z i j +
        negativeEMDWeight coupling phi z * S.firstJet z k i j) U
    have hdrComponent : ContinuousOn (fun z =>
        (negativeEMDWeightDerivative coupling
          (negativeEMDWeight coupling phi z) (v z)) k) U :=
      continuousOn_pi.mp hdr k
    have hfieldComponent : ContinuousOn (fun z => S.field z i j) U :=
      by
        simpa only [matrixContinuousBilinForm4_coordinateDirection] using
          (continuousOn_clm_apply.mp
            (continuousOn_clm_apply.mp hfield (coordinateDirection i))
            (coordinateDirection j))
    have hfirstJetComponent : ContinuousOn
        (fun z => S.firstJet z k i j) U :=
      S.firstJet_continuous k i j
    exact (hdrComponent.mul hfieldComponent).add
      (hweight.mul hfirstJetComponent)
  exact hphysicalFDeriv

/-- **Field-level Maxwell unweighting theorem.** A genuine `C¹` rescaled
matrix field whose accepted Phase-III exponential-weight exterior jet
vanishes produces the exact `IsC1ClosedTwoFormOn` package required by radial
potential recovery. -/
theorem physicalField_isC1ClosedTwoFormOn
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hphi : ∀ z ∈ U,
      HasFDerivAt phi (oneForm4ContinuousLinearMap (v z)) z)
    (hv : ContinuousOn v U)
    (hclosure : ∀ z ∈ U,
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo
        (negativeEMDWeight coupling phi z)
        (negativeEMDWeightDerivative coupling
          (negativeEMDWeight coupling phi z) (v z))
        (S.field z) (matrixExteriorDerivative (S.firstJet z)) = 0) :
    IsC1ClosedTwoFormOn (S.physicalField coupling phi)
      (S.physicalFDeriv coupling phi v) U where
  isOpen := hopen
  starShaped := hstar
  alternating := by
    intro z hz u w
    apply matrixContinuousBilinForm4_alternating_of_transpose_eq_neg
    simp only [physicalMatrix]
    rw [Matrix.transpose_smul, S.alternating z hz]
    simp only [smul_neg]
  differentiable := by
    intro z hz
    exact S.hasFDerivAt_physicalField coupling phi v hphi hz
  derivContinuousOn := S.continuousOn_physicalFDeriv coupling phi v hphi hv
  closed := by
    intro z hz a b c
    apply matrixFirstJetBilinFDeriv_closed_of_exterior_zero
    change matrixExteriorDerivative
      (scaledTwoFormFirstJet
        (negativeEMDWeight coupling phi z)
        (negativeEMDWeightDerivative coupling
          (negativeEMDWeight coupling phi z) (v z))
        (S.field z) (S.firstJet z)) = 0
    rw [matrixExteriorDerivative_scaledTwoFormFirstJet]
    exact hclosure z hz

/-- Positively weighted rescaled two-form matrix.  When the rescaled field is
the Hodge partner of the Phase-III Maxwell seed, this is the physical weighted
dual flux `exp(a phi / 2) G = exp(a phi) (*F)`. -/
noncomputable def weightedDualMatrix
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (z : BaseCoordinateSpace) : Matrix4 :=
  positiveEMDWeight coupling phi z • S.field z

/-- Product-rule coordinate first jet of the positively weighted dual
flux. -/
noncomputable def weightedDualFirstJet
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (z : BaseCoordinateSpace) : Fin 4 → Matrix4 :=
  scaledTwoFormFirstJet (positiveEMDWeight coupling phi z)
    (positiveEMDWeightDerivative coupling
      (positiveEMDWeight coupling phi z) (v z))
    (S.field z) (S.firstJet z)

/-- Actual continuous-bilinear positively weighted dual-flux field. -/
noncomputable def weightedDualField
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (z : BaseCoordinateSpace) :
    ContinuousBilinForm BaseCoordinateSpace :=
  matrixContinuousBilinForm4 (S.weightedDualMatrix coupling phi z)

/-- Genuine Frechet derivative candidate of the weighted dual-flux field. -/
noncomputable def weightedDualFDeriv
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (z : BaseCoordinateSpace) :
    BaseCoordinateSpace →L[ℝ]
      ContinuousBilinForm BaseCoordinateSpace :=
  matrixFirstJetBilinFDeriv (S.weightedDualFirstJet coupling phi v z)

/-- Coordinate form of the derivative of the positive EMD weight. -/
theorem oneForm4ContinuousLinearMap_positiveEMDWeightDerivative
    (coupling r : ℝ) (v : OneForm4) :
    oneForm4ContinuousLinearMap
        (positiveEMDWeightDerivative coupling r v) =
      ((coupling / 2) * r) • oneForm4ContinuousLinearMap v := by
  rw [positiveEMDWeightDerivative,
    oneForm4ContinuousLinearMap_smul]

/-- The displayed positive-weight first jet is the actual Frechet derivative
of the weighted dual-flux field. -/
theorem hasFDerivAt_weightedDualField
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (hphi : ∀ z ∈ U,
      HasFDerivAt phi (oneForm4ContinuousLinearMap (v z)) z)
    {z : BaseCoordinateSpace} (hz : z ∈ U) :
    HasFDerivAt (S.weightedDualField coupling phi)
      (S.weightedDualFDeriv coupling phi v z) z := by
  have hweight :
      HasFDerivAt (positiveEMDWeight coupling phi)
        (((coupling / 2) * positiveEMDWeight coupling phi z) •
          oneForm4ContinuousLinearMap (v z)) z :=
    hasFDerivAt_positiveEMDWeight coupling (hphi z hz)
  have hproduct :
      HasFDerivAt
        ((positiveEMDWeight coupling phi) •
          (fun y => matrixContinuousBilinForm4 (S.field y)))
        (positiveEMDWeight coupling phi z •
            matrixFirstJetBilinFDeriv (S.firstJet z) +
          (((coupling / 2) * positiveEMDWeight coupling phi z) •
            oneForm4ContinuousLinearMap (v z)).smulRight
              (matrixContinuousBilinForm4 (S.field z))) z :=
    hweight.smul (S.differentiable z hz)
  rw [show S.weightedDualField coupling phi =
      (positiveEMDWeight coupling phi) •
        (fun y => matrixContinuousBilinForm4 (S.field y)) by
    funext y
    change matrixContinuousBilinForm4
      (positiveEMDWeight coupling phi y • S.field y) =
        positiveEMDWeight coupling phi y •
          matrixContinuousBilinForm4 (S.field y)
    exact matrixContinuousBilinForm4_smul _ _]
  change HasFDerivAt
    ((positiveEMDWeight coupling phi) •
      (fun y => matrixContinuousBilinForm4 (S.field y)))
    (matrixFirstJetBilinFDeriv
      (scaledTwoFormFirstJet
        (positiveEMDWeight coupling phi z)
        (positiveEMDWeightDerivative coupling
          (positiveEMDWeight coupling phi z) (v z))
        (S.field z) (S.firstJet z))) z
  rw [matrixFirstJetBilinFDeriv_scaledTwoFormFirstJet]
  simpa only [
    oneForm4ContinuousLinearMap_positiveEMDWeightDerivative] using hproduct

/-- Continuity of the scalar one-form and rescaled first jet makes the full
weighted dual-flux derivative field continuous. -/
theorem continuousOn_weightedDualFDeriv
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (hphi : ∀ z ∈ U,
      HasFDerivAt phi (oneForm4ContinuousLinearMap (v z)) z)
    (hv : ContinuousOn v U) :
    ContinuousOn (S.weightedDualFDeriv coupling phi v) U := by
  have hphiContinuous : ContinuousOn phi U :=
    fun z hz => ((hphi z hz).continuousAt).continuousWithinAt
  have hweight : ContinuousOn (positiveEMDWeight coupling phi) U := by
    change ContinuousOn (fun z => Real.exp ((coupling / 2) * phi z)) U
    have hconstant : ContinuousOn
        (fun _ : BaseCoordinateSpace => coupling / 2) U :=
      continuousOn_const
    exact (hconstant.mul hphiContinuous).rexp
  have hfield : ContinuousOn
      (fun z => matrixContinuousBilinForm4 (S.field z)) U :=
    fun z hz => ((S.differentiable z hz).continuousAt).continuousWithinAt
  have hdr : ContinuousOn
      (fun z => positiveEMDWeightDerivative coupling
        (positiveEMDWeight coupling phi z) (v z)) U := by
    change ContinuousOn (fun z =>
      ((coupling / 2) * positiveEMDWeight coupling phi z) • v z) U
    exact ((continuousOn_const.mul hweight).smul hv)
  have hweightedFDeriv : ContinuousOn
      (fun z => matrixFirstJetBilinFDeriv
        (S.weightedDualFirstJet coupling phi v z)) U := by
    apply continuousOn_matrixFirstJetBilinFDeriv
    intro k i j
    change ContinuousOn (fun z =>
      (positiveEMDWeightDerivative coupling
          (positiveEMDWeight coupling phi z) (v z)) k *
          S.field z i j +
        positiveEMDWeight coupling phi z * S.firstJet z k i j) U
    have hdrComponent : ContinuousOn (fun z =>
        (positiveEMDWeightDerivative coupling
          (positiveEMDWeight coupling phi z) (v z)) k) U :=
      continuousOn_pi.mp hdr k
    have hfieldComponent : ContinuousOn (fun z => S.field z i j) U := by
      simpa only [matrixContinuousBilinForm4_coordinateDirection] using
        (continuousOn_clm_apply.mp
          (continuousOn_clm_apply.mp hfield (coordinateDirection i))
          (coordinateDirection j))
    have hfirstJetComponent : ContinuousOn
        (fun z => S.firstJet z k i j) U :=
      S.firstJet_continuous k i j
    exact (hdrComponent.mul hfieldComponent).add
      (hweight.mul hfirstJetComponent)
  exact hweightedFDeriv

/-- **Field-level weighted-dual theorem.** A genuine `C¹` realization of the
rescaled Hodge channel whose positive-weight exterior jet vanishes produces
an actual closed `C¹` weighted dual flux. -/
theorem weightedDualField_isC1ClosedTwoFormOn
    (S : RescaledMaxwellMatrixC1On U)
    (coupling : ℝ) (phi : BaseCoordinateSpace → ℝ)
    (v : BaseCoordinateSpace → OneForm4)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hphi : ∀ z ∈ U,
      HasFDerivAt phi (oneForm4ContinuousLinearMap (v z)) z)
    (hv : ContinuousOn v U)
    (hclosure : ∀ z ∈ U,
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo
        (positiveEMDWeight coupling phi z)
        (positiveEMDWeightDerivative coupling
          (positiveEMDWeight coupling phi z) (v z))
        (S.field z) (matrixExteriorDerivative (S.firstJet z)) = 0) :
    IsC1ClosedTwoFormOn (S.weightedDualField coupling phi)
      (S.weightedDualFDeriv coupling phi v) U where
  isOpen := hopen
  starShaped := hstar
  alternating := by
    intro z hz u w
    apply matrixContinuousBilinForm4_alternating_of_transpose_eq_neg
    simp only [weightedDualMatrix]
    rw [Matrix.transpose_smul, S.alternating z hz]
    simp only [smul_neg]
  differentiable := by
    intro z hz
    exact S.hasFDerivAt_weightedDualField coupling phi v hphi hz
  derivContinuousOn :=
    S.continuousOn_weightedDualFDeriv coupling phi v hphi hv
  closed := by
    intro z hz a b c
    apply matrixFirstJetBilinFDeriv_closed_of_exterior_zero
    change matrixExteriorDerivative
      (scaledTwoFormFirstJet
        (positiveEMDWeight coupling phi z)
        (positiveEMDWeightDerivative coupling
          (positiveEMDWeight coupling phi z) (v z))
        (S.field z) (S.firstJet z)) = 0
    rw [matrixExteriorDerivative_scaledTwoFormFirstJet]
    exact hclosure z hz

end RescaledMaxwellMatrixC1On

namespace CurvatureScalarBranchComponentPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- The abstract branch one-form is exactly the continuous linear map whose
coefficients are the coordinate value used by the Phase-III obstruction
test. -/
theorem branchScalarOneForm_eq_coordinateValue
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) :
    C.branchScalarOneForm branch z =
      oneForm4ContinuousLinearMap
        (C.branchScalarOneFormValue branch z) := by
  cases branch with
  | plus =>
      ext u
      simp [branchScalarOneForm, branchScalarOneFormValue,
        plusField, alphaField, betaField,
        CurvatureScalarBranchJet4.vPlus,
        oneForm4ContinuousLinearMap_apply, oneForm4Evaluate]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
  | minus =>
      ext u
      simp [branchScalarOneForm, branchScalarOneFormValue,
        minusField, alphaField, betaField,
        CurvatureScalarBranchJet4.vMinus,
        oneForm4ContinuousLinearMap_apply, oneForm4Evaluate]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The coordinate value of either reconstructed scalar branch is continuous
on the patch.  This follows from the already-proved differentiability of its
two genuine spectral-component one-form fields. -/
theorem continuousOn_branchScalarOneFormValue
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4) :
    ContinuousOn (C.branchScalarOneFormValue branch) U := by
  have hfield : ContinuousOn (C.branchScalarOneForm branch) U := by
    cases branch with
    | plus =>
        exact (C.alphaDifferentiable.add C.betaDifferentiable).continuousOn
    | minus =>
        exact (C.alphaDifferentiable.sub C.betaDifferentiable).continuousOn
  rw [continuousOn_pi]
  intro i
  have happly := continuousOn_clm_apply.mp hfield (coordinateDirection i)
  simpa only [C.branchScalarOneForm_eq_coordinateValue branch,
    oneForm4ContinuousLinearMap_coordinateDirection] using happly

end CurvatureScalarBranchComponentPatch4

/-- Actual rescaled Maxwell field data matching the accepted Phase-III
coordinate seed.  The two equalities state that its value and exteriorized
first jet are precisely the `rotatedF` data tested by the obstruction
classifier. -/
structure PositiveQPhaseIIIRescaledMaxwellC1Realization
    {U : Set CurvatureCoordinateSpace4}
    (M : PositiveQPhaseIIIPatch4 U) where
  c1 : RescaledMaxwellMatrixC1On U
  field_eq : ∀ z ∈ U, c1.field z = (M.exteriorJet z).rotatedF
  exteriorFirstJet_eq : ∀ z ∈ U,
    matrixExteriorDerivative (c1.firstJet z) =
      (M.exteriorJet z).rotatedDF matrixOneWedgeTwo

/-- Actual `C¹` realizations of both rescaled Phase-III channels.  Keeping the
Hodge channel here prevents the weighted Maxwell equation from being hidden
inside the later normal-gauge EMD certificate. -/
structure PositiveQPhaseIIIRescaledMaxwellC1PairRealization
    {U : Set CurvatureCoordinateSpace4}
    (M : PositiveQPhaseIIIPatch4 U) where
  maxwell : PositiveQPhaseIIIRescaledMaxwellC1Realization M
  hodge : RescaledMaxwellMatrixC1On U
  hodge_field_eq : ∀ z ∈ U,
    hodge.field z = (M.exteriorJet z).rotatedG
  hodge_exteriorFirstJet_eq : ∀ z ∈ U,
    matrixExteriorDerivative (hodge.firstJet z) =
      (M.exteriorJet z).rotatedDG matrixOneWedgeTwo

/-- Field-level output of an accepted curvature/Phase-III branch: a selected
scalar representative and the matching genuine closed `C¹` physical Maxwell
two-form required by radial potential recovery. -/
structure PhaseIIIPhysicalMaxwellC1Realization
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (branch : RelativeSignScalarBranch4) where
  scalarRepresentative : CurvatureCoordinateSpace4 → ℝ
  scalarRepresentative_is :
    IsScalarPotentialOn scalarRepresentative
      (C.branchScalarOneForm branch) U
  physicalMaxwell : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4
  physicalMaxwellDerivative :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ]
      ContinuousBilinForm CurvatureCoordinateSpace4
  physicalMaxwell_closed :
    IsC1ClosedTwoFormOn physicalMaxwell physicalMaxwellDerivative U
  physicalMaxwell_matches_unweightedSeed :
    ∀ z ∈ U, ∀ i j,
      physicalMaxwell z (coordinateDirection i) (coordinateDirection j) =
        negativeEMDWeight M.coupling scalarRepresentative z *
          (M.exteriorJet z).rotatedF i j

/-- Field-level output retaining both consequences of Phase-III acceptance:
the closed physical Maxwell field and the closed positively weighted Hodge
flux.  The final metric-Hodge identification remains an explicit downstream
obligation. -/
structure PhaseIIIPhysicalMaxwellC1PairRealization
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (branch : RelativeSignScalarBranch4) where
  maxwell : PhaseIIIPhysicalMaxwellC1Realization C M branch
  weightedHodgeFlux : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4
  weightedHodgeFluxDerivative :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ]
      ContinuousBilinForm CurvatureCoordinateSpace4
  weightedHodgeFlux_closed :
    IsC1ClosedTwoFormOn weightedHodgeFlux
      weightedHodgeFluxDerivative U
  weightedHodgeFlux_matches_seed :
    ∀ z ∈ U, ∀ i j,
      weightedHodgeFlux z (coordinateDirection i) (coordinateDirection j) =
        positiveEMDWeight M.coupling maxwell.scalarRepresentative z *
          (M.exteriorJet z).rotatedG i j

/-- Obligations remaining after the physical Maxwell field has been produced:
the convention-fixed Kaluza coupling and a compatible normal-gauge `C²` EMD
realizer.  The scalar and Maxwell field-level data are no longer repeated. -/
structure PhaseIIINormalGaugeCompletionAt
    {U : Set CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch)
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  scalarValueAtPoint : ℝ
  scalarRepresentative_value :
    P.scalarRepresentative x = scalarValueAtPoint
  coupling_is_kaluza : IsKaluzaCoupling M.coupling
  realize :
    (phi : CurvatureCoordinateSpace4 → ℝ) →
      IsScalarPotentialOn phi (C.branchScalarOneForm branch) U →
      phi x = scalarValueAtPoint →
      (A : CurvatureCoordinateSpace4 →
        CurvatureCoordinateSpace4 →L[ℝ] ℝ) →
      IsGaugePotentialOn A P.physicalMaxwell U →
      LorentzianKaluzaLocalProductGermAt x
  realize_scalar :
    ∀ phi hphi hvalue A hA,
      (realize phi hphi hvalue A hA).fields.phi = phi
  realize_potential :
    ∀ phi hphi hvalue A hA y i,
      (realize phi hphi hvalue A hA).fields.potential y i =
        A y (coordinateDirection i)
  realize_emd :
    ∀ phi hphi hvalue A hA,
      (realize phi hphi hvalue A hA).fields.EMDEquations

namespace PhaseIIIPhysicalMaxwellC1Realization

variable {U : Set CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {x : CurvatureCoordinateSpace4}

/-- Convention-registry Maxwell field `F`, obtained from the legacy
curvature-normalized realization `F / sqrt 2`. -/
noncomputable def conventionNormalizedPhysicalMaxwell
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch) :
    CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4 :=
  Real.sqrt 2 • P.physicalMaxwell

/-- Frechet derivative field of the convention-registry Maxwell field. -/
noncomputable def conventionNormalizedPhysicalMaxwellDerivative
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ]
      ContinuousBilinForm CurvatureCoordinateSpace4 :=
  Real.sqrt 2 • P.physicalMaxwellDerivative

/-- **Normalization bridge.** The convention-registry field `F` inherits the
complete closed `C¹` two-form package from the legacy `F / sqrt 2`
realization by constant scaling. -/
theorem conventionNormalizedPhysicalMaxwell_closed
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch) :
    IsC1ClosedTwoFormOn P.conventionNormalizedPhysicalMaxwell
      P.conventionNormalizedPhysicalMaxwellDerivative U := by
  exact P.physicalMaxwell_closed.const_smul (Real.sqrt 2)

/-- Coordinate values of the convention-registry field match
`sqrt 2 * exp(-a phi / 2) H`, the normalization used by the EMD and Kaluza
uplift convention registry. -/
theorem conventionNormalizedPhysicalMaxwell_matches_seed
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch)
    {z : CurvatureCoordinateSpace4} (hz : z ∈ U) (i j : Fin 4) :
    P.conventionNormalizedPhysicalMaxwell z
        (coordinateDirection i) (coordinateDirection j) =
      Real.sqrt 2 *
        negativeEMDWeight M.coupling P.scalarRepresentative z *
          (M.exteriorJet z).rotatedF i j := by
  change Real.sqrt 2 *
      P.physicalMaxwell z (coordinateDirection i) (coordinateDirection j) = _
  rw [P.physicalMaxwell_matches_unweightedSeed z hz i j]
  ring

/-- Scaling a potential for the legacy field by `sqrt 2` gives a potential
for the convention-registry Maxwell field. -/
theorem conventionNormalizedPhysicalMaxwell_gaugePotential
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch)
    {A : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ}
    (hA : IsGaugePotentialOn A P.physicalMaxwell U) :
    IsGaugePotentialOn (Real.sqrt 2 • A)
      P.conventionNormalizedPhysicalMaxwell U := by
  exact hA.const_smul (Real.sqrt 2)

/-- The closed convention-registry field has an explicit potential obtained
by multiplying a potential of the legacy realization by `sqrt 2`. -/
theorem exists_conventionNormalizedPhysicalMaxwell_gaugePotential
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch) :
    ∃ A : CurvatureCoordinateSpace4 →
        CurvatureCoordinateSpace4 →L[ℝ] ℝ,
      IsGaugePotentialOn A P.physicalMaxwell U ∧
        IsGaugePotentialOn (Real.sqrt 2 • A)
          P.conventionNormalizedPhysicalMaxwell U := by
  obtain ⟨A, hA⟩ := exists_gaugePotentialOn_of_closed
    P.physicalMaxwell_closed
  exact ⟨A, hA, P.conventionNormalizedPhysicalMaxwell_gaugePotential hA⟩

/-- Insert the constructed scalar/Maxwell package into the former broad
conditional-uplift interface. -/
def toConditionalUpliftCompletionAt
    (P : PhaseIIIPhysicalMaxwellC1Realization C M branch)
    (N : PhaseIIINormalGaugeCompletionAt P x) :
    ConditionalUpliftCompletionAt C M branch x where
  point_mem := N.point_mem
  scalarValueAtPoint := N.scalarValueAtPoint
  scalarRepresentative := P.scalarRepresentative
  scalarRepresentative_is := P.scalarRepresentative_is
  scalarRepresentative_value := N.scalarRepresentative_value
  physicalMaxwell := P.physicalMaxwell
  physicalMaxwellDerivative := P.physicalMaxwellDerivative
  physicalMaxwell_closed := P.physicalMaxwell_closed
  physicalMaxwell_matches_unweightedSeed :=
    P.physicalMaxwell_matches_unweightedSeed
  coupling_is_kaluza := N.coupling_is_kaluza
  realize := N.realize
  realize_scalar := N.realize_scalar
  realize_potential := N.realize_potential
  realize_emd := N.realize_emd

end PhaseIIIPhysicalMaxwellC1Realization

namespace PhaseIIIAcceptedBranch

variable {U : Set CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- **Accepted-jet to physical-field theorem.** Once the displayed rescaled
seed and first jet are realized by an actual `C¹` matrix two-form, Phase-III
acceptance canonically unweights it to the matching closed physical Maxwell
field.  No further Maxwell differential equation is assumed. -/
noncomputable def toPhysicalMaxwellC1Realization
    (A : PhaseIIIAcceptedBranch C M branch)
    (R : PositiveQPhaseIIIRescaledMaxwellC1Realization M)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U) :
    PhaseIIIPhysicalMaxwellC1Realization C M branch := by
  classical
  let phi := Classical.choose A.scalar
  have hphi : IsScalarPotentialOn phi
      (C.branchScalarOneForm branch) U :=
    Classical.choose_spec A.scalar
  have hphiCoordinate : ∀ z ∈ U,
      HasFDerivAt phi
        (oneForm4ContinuousLinearMap
          (C.branchScalarOneFormValue branch z)) z := by
    intro z hz
    rw [← C.branchScalarOneForm_eq_coordinateValue branch z]
    exact hphi z hz
  have hclosures :=
    M.branchObstructionsVanishOn_gives_closed_exponentialWeightJets
      C branch A.maxwell (negativeEMDWeight M.coupling phi)
        (positiveEMDWeight M.coupling phi)
  have hclosure : ∀ z ∈ U,
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo
        (negativeEMDWeight M.coupling phi z)
        (negativeEMDWeightDerivative M.coupling
          (negativeEMDWeight M.coupling phi z)
          (C.branchScalarOneFormValue branch z))
        (R.c1.field z)
        (matrixExteriorDerivative (R.c1.firstJet z)) = 0 := by
    intro z hz
    rw [R.field_eq z hz, R.exteriorFirstJet_eq z hz]
    exact (hclosures z hz).1
  exact {
    scalarRepresentative := phi
    scalarRepresentative_is := hphi
    physicalMaxwell := R.c1.physicalField M.coupling phi
    physicalMaxwellDerivative := R.c1.physicalFDeriv M.coupling phi
      (C.branchScalarOneFormValue branch)
    physicalMaxwell_closed :=
      R.c1.physicalField_isC1ClosedTwoFormOn M.coupling phi
        (C.branchScalarOneFormValue branch) hopen hstar hphiCoordinate
        (C.continuousOn_branchScalarOneFormValue branch) hclosure
    physicalMaxwell_matches_unweightedSeed := by
      intro z hz i j
      simp only [RescaledMaxwellMatrixC1On.physicalField,
        RescaledMaxwellMatrixC1On.physicalMatrix,
        matrixContinuousBilinForm4_coordinateDirection,
        Matrix.smul_apply, smul_eq_mul]
      rw [R.field_eq z hz]
  }

/-- The curvature-to-uplift composition now requires only a realized
rescaled Maxwell first jet and the reduced normal-gauge completion package.
The physical closed `C¹` field is constructed internally. -/
theorem exists_completeConditionalKaluzaUplift_of_rescaledMaxwellC1
    (A : PhaseIIIAcceptedBranch C M branch)
    (R : PositiveQPhaseIIIRescaledMaxwellC1Realization M)
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (hstar : StarConvex ℝ 0 U)
    {x : CurvatureCoordinateSpace4}
    (N : PhaseIIINormalGaugeCompletionAt
      (A.toPhysicalMaxwellC1Realization R hopen hstar) x) :
    Nonempty (CompleteConditionalKaluzaUplift
      (((A.toPhysicalMaxwellC1Realization R hopen hstar).toConditionalUpliftCompletionAt
        N).toAcceptedKaluzaBranchAt A
          hconvex hopen)) := by
  exact ConditionalUpliftCompletionAt.exists_completeConditionalKaluzaUplift_of_phaseIIIAccepted
    A ((A.toPhysicalMaxwellC1Realization R hopen hstar).toConditionalUpliftCompletionAt
      N) hconvex hopen

end PhaseIIIAcceptedBranch

end RainichKaluza
