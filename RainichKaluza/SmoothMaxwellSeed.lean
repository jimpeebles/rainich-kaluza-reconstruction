import RainichKaluza.SmoothPrincipalPlaneFrame

/-!
# Smooth Maxwell seeds in a local trivialization

A smooth principal tetrad gives a smooth frame matrix.  Combining that matrix
with the explicit positive-`q` canonical two-form produces a smooth local
Maxwell seed.  The pointwise covariance theorems then identify its stress with
the transported residual.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Select one vector from a varying principal tetrad. -/
def smoothPrincipalTetradVector
    (T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ)))
    (j : Fin 4) (z : X) : Fin 4 → ℝ :=
  principalTetradVectors (T z).1 (T z).2 j

/-- Every column of a smooth principal tetrad is smooth. -/
theorem contDiffOn_smoothPrincipalTetradVector
    {n : WithTop ℕ∞} {U : Set X}
    {T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ))}
    (hT : ContDiffOn ℝ n T U) (j : Fin 4) :
    ContDiffOn ℝ n (smoothPrincipalTetradVector T j) U := by
  fin_cases j
  · change ContDiffOn ℝ n (fun z => (T z).1.1) U
    exact hT.fst.fst
  · change ContDiffOn ℝ n (fun z => (T z).1.2) U
    exact hT.fst.snd
  · change ContDiffOn ℝ n (fun z => (T z).2.1) U
    exact hT.snd.fst
  · change ContDiffOn ℝ n (fun z => (T z).2.2) U
    exact hT.snd.snd

/-- Matrix whose columns are the four vectors of a principal tetrad. -/
def smoothPrincipalFrameMatrix
    (T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ)))
    (z : X) : Matrix4 :=
  fun i j => smoothPrincipalTetradVector T j z i

/-- Minkowski bilinear form in the standard coordinate basis. -/
noncomputable def minkowskiBilinForm :
    LinearMap.BilinForm ℝ (Fin 4 → ℝ) :=
  Matrix.toBilin (Pi.basisFun ℝ (Fin 4)) minkowskiMetric

/-- The standard-coordinate matrix of the Minkowski bilinear form is `G`. -/
@[simp]
theorem minkowskiBilinForm_toMatrix :
    LinearMap.BilinForm.toMatrix (Pi.basisFun ℝ (Fin 4))
      minkowskiBilinForm = minkowskiMetric := by
  simp [minkowskiBilinForm]

/-- A smooth coframe matrix is the transpose of the column frame matrix. -/
def smoothPrincipalCoframeMatrix
    (T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ)))
    (z : X) : Matrix4 :=
  (smoothPrincipalFrameMatrix T z)ᵀ

/-- Entrywise `C^n` regularity for a matrix field.  Mathlib deliberately does
not place a canonical matrix norm on this type, so this is the coordinate-
invariant finite-dimensional formulation needed here. -/
def MatrixFieldContDiffOn
    (n : WithTop ℕ∞) (U : Set X) (A : X → Matrix4) : Prop :=
  ∀ i j, ContDiffOn ℝ n (fun z => A z i j) U

/-- Pointwise constructive cosine coordinate of a smooth canonical Maxwell
stress fibre. -/
noncomputable def smoothCanonicalStressFiberCosine
    (q : X → ℝ) (F : X → Matrix4) (z : X) : ℝ :=
  canonicalStressFiberCosine (q z) (F z)

/-- Pointwise constructive sine coordinate of a smooth canonical Maxwell
stress fibre. -/
noncomputable def smoothCanonicalStressFiberSine
    (q : X → ℝ) (F : X → Matrix4) (z : X) : ℝ :=
  canonicalStressFiberSine (q z) (F z)

/-- The constructive stress-fibre cosine is as smooth as the physical
two-form and positive stress magnitude. -/
theorem contDiffOn_smoothCanonicalStressFiberCosine
    {n : WithTop ℕ∞} {U : Set X} {q : X → ℝ} {F : X → Matrix4}
    (hqSmooth : ContDiffOn ℝ n q U)
    (hF : MatrixFieldContDiffOn n U F)
    (hq : ∀ z ∈ U, 0 < q z) :
    ContDiffOn ℝ n (smoothCanonicalStressFiberCosine q F) U := by
  have harg : ContDiffOn ℝ n (fun z => 2 * q z) U :=
    contDiffOn_const.mul hqSmooth
  have hsqrt : ContDiffOn ℝ n (fun z => Real.sqrt (2 * q z)) U :=
    harg.sqrt (fun z hz => by linarith [hq z hz])
  exact (hF 0 1).div hsqrt
    (fun z hz => Real.sqrt_ne_zero'.mpr (by linarith [hq z hz]))

/-- The constructive stress-fibre sine is equally smooth. -/
theorem contDiffOn_smoothCanonicalStressFiberSine
    {n : WithTop ℕ∞} {U : Set X} {q : X → ℝ} {F : X → Matrix4}
    (hqSmooth : ContDiffOn ℝ n q U)
    (hF : MatrixFieldContDiffOn n U F)
    (hq : ∀ z ∈ U, 0 < q z) :
    ContDiffOn ℝ n (smoothCanonicalStressFiberSine q F) U := by
  have harg : ContDiffOn ℝ n (fun z => 2 * q z) U :=
    contDiffOn_const.mul hqSmooth
  have hsqrt : ContDiffOn ℝ n (fun z => Real.sqrt (2 * q z)) U :=
    harg.sqrt (fun z hz => by linarith [hq z hz])
  exact (hF 2 3).div hsqrt
    (fun z hz => Real.sqrt_ne_zero'.mpr (by linarith [hq z hz]))

/-- **Smooth local Maxwell stress-fibre theorem.** A smooth skew two-form
with the positive canonical non-null stress admits explicit smooth unit-circle
duality coordinates, and those coordinates reconstruct the whole field at
every point of the patch. -/
theorem smoothCanonicalStressFiber_coordinates
    {n : WithTop ℕ∞} {U : Set X} {q : X → ℝ} {F : X → Matrix4}
    (hqSmooth : ContDiffOn ℝ n q U)
    (hFsmooth : MatrixFieldContDiffOn n U F)
    (hq : ∀ z ∈ U, 0 < q z)
    (hskew : ∀ z ∈ U, (F z)ᵀ = -F z)
    (hstress : ∀ z ∈ U,
      matrixMaxwellStress minkowskiMetric (F z) =
        canonicalMaxwellResidual (q z)) :
    ContDiffOn ℝ n (smoothCanonicalStressFiberCosine q F) U ∧
      ContDiffOn ℝ n (smoothCanonicalStressFiberSine q F) U ∧
      (∀ z ∈ U,
        smoothCanonicalStressFiberCosine q F z ^ 2 +
          smoothCanonicalStressFiberSine q F z ^ 2 = 1) ∧
      ∀ z ∈ U,
        F z = smoothCanonicalStressFiberCosine q F z •
              canonicalMaxwellTwoForm (Real.sqrt (2 * q z)) 0 +
            smoothCanonicalStressFiberSine q F z •
              canonicalHodgeStar (Real.sqrt (2 * q z)) 0 := by
  refine ⟨contDiffOn_smoothCanonicalStressFiberCosine
      hqSmooth hFsmooth hq,
    contDiffOn_smoothCanonicalStressFiberSine hqSmooth hFsmooth hq,
    ?_, ?_⟩
  · intro z hz
    exact (canonicalStressFiber_coordinates
      (F z) (q z) (hq z hz) (hskew z hz) (hstress z hz)).1
  · intro z hz
    exact (canonicalStressFiber_coordinates
      (F z) (q z) (hq z hz) (hskew z hz) (hstress z hz)).2

/-- A smooth varying change of coframe preserves entrywise smoothness of a
covariant two-form. -/
theorem contDiffOn_transportTwoForm_fields
    {n : WithTop ℕ∞} {U : Set X} {K F : X → Matrix4}
    (hK : MatrixFieldContDiffOn n U K)
    (hF : MatrixFieldContDiffOn n U F) :
    MatrixFieldContDiffOn n U
      (fun z => transportTwoForm (K z) (F z)) := by
  intro i j
  simp only [transportTwoForm, Matrix.mul_apply, Matrix.transpose_apply]
  exact ContDiffOn.sum fun k _ =>
    (ContDiffOn.sum fun l _ => (hK l i).mul (hF l k)).mul (hK k j)

/-- **Smooth arbitrary-frame Maxwell stress-fibre theorem.** If smooth
varying coframe/frame fields are mutual inverses and carry the inverse metric
and Maxwell stress into canonical Lorentz form, then the pulled physical
two-form has explicit smooth unit-circle duality coordinates throughout the
patch. This is the patchwise upgrade of
`adaptedMaxwellStressFiber_coordinates`; no discontinuous choice of angle or
existential duality parameter is made. -/
theorem smoothAdaptedMaxwellStressFiber_coordinates
    {n : WithTop ℕ∞} {U : Set X}
    (GInv L K F : X → Matrix4) (q : X → ℝ)
    (hqSmooth : ContDiffOn ℝ n q U)
    (hKSmooth : MatrixFieldContDiffOn n U K)
    (hFSmooth : MatrixFieldContDiffOn n U F)
    (hq : ∀ z ∈ U, 0 < q z)
    (hKL : ∀ z ∈ U, K z * L z = 1)
    (hLK : ∀ z ∈ U, L z * K z = 1)
    (hmetric : ∀ z ∈ U,
      L z * GInv z * (L z)ᵀ = minkowskiMetric)
    (hskew : ∀ z ∈ U, (F z)ᵀ = -F z)
    (hstress : ∀ z ∈ U,
      transportMixed (L z) (matrixMaxwellStress (GInv z) (F z)) (K z) =
        canonicalMaxwellResidual (q z)) :
    let pulledF := fun z => transportTwoForm (K z) (F z)
    ContDiffOn ℝ n (smoothCanonicalStressFiberCosine q pulledF) U ∧
      ContDiffOn ℝ n (smoothCanonicalStressFiberSine q pulledF) U ∧
      (∀ z ∈ U,
        smoothCanonicalStressFiberCosine q pulledF z ^ 2 +
          smoothCanonicalStressFiberSine q pulledF z ^ 2 = 1) ∧
      ∀ z ∈ U,
        pulledF z = smoothCanonicalStressFiberCosine q pulledF z •
              canonicalMaxwellTwoForm (Real.sqrt (2 * q z)) 0 +
            smoothCanonicalStressFiberSine q pulledF z •
              canonicalHodgeStar (Real.sqrt (2 * q z)) 0 := by
  dsimp only
  apply smoothCanonicalStressFiber_coordinates
    hqSmooth (contDiffOn_transportTwoForm_fields hKSmooth hFSmooth) hq
  · intro z hz
    exact transportTwoForm_transpose (K z) (F z) (hskew z hz)
  · intro z hz
    rw [← hmetric z hz]
    exact (matrixMaxwellStress_changeBasis
      (GInv z) (L z) (K z) (F z)
      (hKL z hz) (hLK z hz)).trans (hstress z hz)

/-- A smooth principal tetrad has a smooth frame matrix. -/
theorem contDiffOn_smoothPrincipalFrameMatrix
    {n : WithTop ℕ∞} {U : Set X}
    {T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ))}
    (hT : ContDiffOn ℝ n T U) :
    MatrixFieldContDiffOn n U (smoothPrincipalFrameMatrix T) := by
  intro i j
  exact contDiffOn_pi.mp (contDiffOn_smoothPrincipalTetradVector hT j) i

set_option linter.unusedSectionVars false in
/-- The column matrix of a pseudo-orthonormal tetrad pulls the coordinate
metric matrix back to the canonical Minkowski matrix.  This version is valid
for an arbitrary coordinate metric, rather than only a Minkowski
trivialization. -/
theorem smoothPrincipalFrameMatrix_metric
    (T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ))) (z : X)
    (g : LinearMap.BilinForm ℝ (Fin 4 → ℝ)) (G : Matrix4)
    (hG : Matrix.toBilin' G = g)
    (hgsymm : g.IsSymm)
    (hframe : IsPseudoOrthonormalPrincipalTetrad g (T z).1 (T z).2) :
    (smoothPrincipalFrameMatrix T z)ᵀ * G *
        smoothPrincipalFrameMatrix T z = minkowskiMetric := by
  let E := smoothPrincipalFrameMatrix T z
  have hentry (i j : Fin 4) :
      (Eᵀ * G * E) i j =
        g (smoothPrincipalTetradVector T i z)
          (smoothPrincipalTetradVector T j z) := by
    rw [← hG]
    simp only [Matrix.toBilin'_apply,
      Matrix.mul_apply, Matrix.transpose_apply, E, smoothPrincipalFrameMatrix]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  rcases hframe with
    ⟨⟨h00, h11, h01⟩, ⟨h22, h33, h23⟩,
      ⟨h02, h03, h12, h13⟩⟩
  have h10 := hgsymm.eq (T z).1.2 (T z).1.1
  have h20 := hgsymm.eq (T z).2.1 (T z).1.1
  have h30 := hgsymm.eq (T z).2.2 (T z).1.1
  have h21 := hgsymm.eq (T z).2.1 (T z).1.2
  have h31 := hgsymm.eq (T z).2.2 (T z).1.2
  have h32 := hgsymm.eq (T z).2.2 (T z).2.1
  ext i j
  rw [hentry]
  fin_cases i <;> fin_cases j <;>
    simp [smoothPrincipalTetradVector, principalTetradVectors,
      minkowskiMetric, h00, h11, h01, h10, h20, h30, h21, h31,
      h32, h22, h33, h23, h02, h03, h12, h13] at *

/-- The inverse of the tetrad column matrix is the actual dual coframe in a
general chart and reconstructs the coordinate metric from `minkowskiMetric`.
This is the coordinate identity required for Hodge naturality. -/
theorem inverse_smoothPrincipalFrameMatrix_metric
    (T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ))) (z : X)
    (g : LinearMap.BilinForm ℝ (Fin 4 → ℝ)) (G : Matrix4)
    (hG : Matrix.toBilin' G = g) (hgsymm : g.IsSymm)
    (hframe : IsPseudoOrthonormalPrincipalTetrad g (T z).1 (T z).2) :
    (smoothPrincipalFrameMatrix T z)⁻¹ᵀ * minkowskiMetric *
        (smoothPrincipalFrameMatrix T z)⁻¹ = G := by
  apply inverseFrame_metric_of_frame_metric
  exact smoothPrincipalFrameMatrix_metric T z g G hG hgsymm hframe

/-- Canonical positive-`q` two-form as a varying matrix. -/
noncomputable def smoothCanonicalPositiveQSeed
    (q : X → ℝ) (z : X) : Matrix4 :=
  canonicalMaxwellTwoForm (Real.sqrt (2 * q z)) 0

/-- The canonical positive-`q` seed varies smoothly wherever `q>0`. -/
theorem contDiffOn_smoothCanonicalPositiveQSeed
    {n : WithTop ℕ∞} {U : Set X} {q : X → ℝ}
    (hqSmooth : ContDiffOn ℝ n q U) (hq : ∀ z ∈ U, 0 < q z) :
    MatrixFieldContDiffOn n U (smoothCanonicalPositiveQSeed q) := by
  have harg : ContDiffOn ℝ n (fun z => 2 * q z) U :=
    contDiffOn_const.mul hqSmooth
  have hamp : ContDiffOn ℝ n (fun z => Real.sqrt (2 * q z)) U :=
    harg.sqrt (fun z hz => by linarith [hq z hz])
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [smoothCanonicalPositiveQSeed, canonicalMaxwellTwoForm] <;>
    first | exact contDiffOn_const | exact hamp | exact hamp.neg

/-- Smooth positive-`q` seed transported by a varying frame matrix. -/
noncomputable def smoothTransportedPositiveQSeed
    (L : X → Matrix4) (q : X → ℝ) (z : X) : Matrix4 :=
  transportTwoForm (L z) (smoothCanonicalPositiveQSeed q z)

/-- Transposition preserves smoothness for matrix fields. -/
theorem MatrixFieldContDiffOn.transpose
    {n : WithTop ℕ∞} {U : Set X} {A : X → Matrix4}
    (hA : MatrixFieldContDiffOn n U A) :
    MatrixFieldContDiffOn n U (fun z => (A z)ᵀ) := by
  intro i j
  exact hA j i

/-- The determinant of an entrywise `C^n` real `4 × 4` matrix field is
`C^n`.  This is the finite Leibniz polynomial, so no norm or manifold
structure on the matrix type is needed. -/
theorem MatrixFieldContDiffOn.det
    {n : WithTop ℕ∞} {U : Set X} {A : X → Matrix4}
    (hA : MatrixFieldContDiffOn n U A) :
    ContDiffOn ℝ n (fun z => Matrix.det (A z)) U := by
  simp_rw [Matrix.det_apply]
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.const_smul
  exact contDiffOn_prod fun k _ => hA (σ k) k

/-- The adjugate of an entrywise `C^n` real `4 × 4` matrix field is
entrywise `C^n`. -/
theorem MatrixFieldContDiffOn.adjugate
    {n : WithTop ℕ∞} {U : Set X} {A : X → Matrix4}
    (hA : MatrixFieldContDiffOn n U A) :
    MatrixFieldContDiffOn n U (fun z => Matrix.adjugate (A z)) := by
  intro i j
  rw [show (fun z => Matrix.adjugate (A z) i j) =
      fun z => Matrix.det ((A z).updateRow j (Pi.single i 1)) by
    funext z
    exact Matrix.adjugate_apply (A z) i j]
  apply MatrixFieldContDiffOn.det
  intro r c
  simp only [Matrix.updateRow_apply]
  by_cases hr : r = j
  · simp only [if_pos hr]
    exact contDiffOn_const
  · simp only [if_neg hr]
    exact hA r c

/-- Nonsingular inversion preserves entrywise `C^n` regularity for real
`4 × 4` matrix fields.  This is Cramer's formula
`A⁻¹ = det(A)⁻¹ • adj(A)` with the pointwise nonvanishing determinant
supplying smooth reciprocal regularity. -/
theorem MatrixFieldContDiffOn.inv
    {n : WithTop ℕ∞} {U : Set X} {A : X → Matrix4}
    (hA : MatrixFieldContDiffOn n U A)
    (hdet : ∀ z ∈ U, Matrix.det (A z) ≠ 0) :
    MatrixFieldContDiffOn n U (fun z => (A z)⁻¹) := by
  have hinvDet : ContDiffOn ℝ n
      (fun z => (Matrix.det (A z))⁻¹) U :=
    hA.det.inv hdet
  have hadj := hA.adjugate
  intro i j
  rw [show (fun z => (A z)⁻¹ i j) =
      fun z => (Matrix.det (A z))⁻¹ * Matrix.adjugate (A z) i j by
    funext z
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl]
  exact hinvDet.mul (hadj i j)

/-- A smooth principal tetrad has a smooth coframe matrix. -/
theorem contDiffOn_smoothPrincipalCoframeMatrix
    {n : WithTop ℕ∞} {U : Set X}
    {T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ))}
    (hT : ContDiffOn ℝ n T U) :
    MatrixFieldContDiffOn n U (smoothPrincipalCoframeMatrix T) := by
  exact (contDiffOn_smoothPrincipalFrameMatrix hT).transpose

set_option linter.unusedSectionVars false in
/-- A pseudo-orthonormal tetrad has a Lorentz coframe matrix. -/
theorem smoothPrincipalCoframeMatrix_lorentz
    (T : X → ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
      ((Fin 4 → ℝ) × (Fin 4 → ℝ))) (z : X)
    (hframe : IsPseudoOrthonormalPrincipalTetrad minkowskiBilinForm
      (T z).1 (T z).2) :
    smoothPrincipalCoframeMatrix T z * minkowskiMetric *
        (smoothPrincipalCoframeMatrix T z)ᵀ = minkowskiMetric := by
  let E := smoothPrincipalFrameMatrix T z
  have hentry (i j : Fin 4) :
      (Eᵀ * minkowskiMetric * E) i j =
        minkowskiBilinForm
          (smoothPrincipalTetradVector T i z)
          (smoothPrincipalTetradVector T j z) := by
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
      (Pi.basisFun ℝ (Fin 4))]
    simp only [minkowskiBilinForm_toMatrix, Pi.basisFun_repr,
      dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      E, smoothPrincipalFrameMatrix]
    simp [minkowskiMetric, Fin.sum_univ_succ]
  rcases hframe with
    ⟨⟨h00, h11, h01⟩, ⟨h22, h33, h23⟩,
      ⟨h02, h03, h12, h13⟩⟩
  have hsymm : minkowskiBilinForm.IsSymm := by
    refine ⟨?_⟩
    intro x y
    rw [minkowskiBilinForm]
    simp only [Matrix.toBilin_apply, Pi.basisFun_repr]
    rw [minkowskiMetric]
    simp [Fin.sum_univ_succ]
    ring
  have h10 := hsymm.eq (T z).1.2 (T z).1.1
  have h20 := hsymm.eq (T z).2.1 (T z).1.1
  have h30 := hsymm.eq (T z).2.2 (T z).1.1
  have h21 := hsymm.eq (T z).2.1 (T z).1.2
  have h31 := hsymm.eq (T z).2.2 (T z).1.2
  have h32 := hsymm.eq (T z).2.2 (T z).2.1
  change Eᵀ * minkowskiMetric * E = minkowskiMetric
  ext i j
  rw [hentry]
  fin_cases i <;> fin_cases j <;>
    simp [smoothPrincipalTetradVector, principalTetradVectors,
      minkowskiMetric, h00, h11, h01, h10, h20, h30, h21, h31,
      h32, h22, h33, h23, h02, h03, h12, h13] at *

/-- Entrywise smooth matrix fields are closed under matrix multiplication. -/
theorem MatrixFieldContDiffOn.mul
    {n : WithTop ℕ∞} {U : Set X} {A B : X → Matrix4}
    (hA : MatrixFieldContDiffOn n U A)
    (hB : MatrixFieldContDiffOn n U B) :
    MatrixFieldContDiffOn n U (fun z => A z * B z) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hA i k).mul (hB k j)

/-- A constant matrix field is entrywise smooth. -/
theorem matrixFieldContDiffOn_const
    {n : WithTop ℕ∞} {U : Set X} (A : Matrix4) :
    MatrixFieldContDiffOn n U (fun _ : X => A) := by
  intro i j
  exact contDiffOn_const

/-- The selected Minkowski metric is its own inverse. -/
theorem minkowskiMetric_sq : minkowskiMetric * minkowskiMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Explicit inverse/coframe of a Lorentz frame. -/
def smoothLorentzInverse (L : X → Matrix4) (z : X) : Matrix4 :=
  minkowskiMetric * (L z)ᵀ * minkowskiMetric

/-- The Lorentz inverse is smooth because it is polynomial in the frame
entries. -/
theorem contDiffOn_smoothLorentzInverse
    {n : WithTop ℕ∞} {U : Set X} {L : X → Matrix4}
    (hL : MatrixFieldContDiffOn n U L) :
    MatrixFieldContDiffOn n U (smoothLorentzInverse L) := by
  have hG : MatrixFieldContDiffOn n U (fun _ : X => minkowskiMetric) :=
    matrixFieldContDiffOn_const minkowskiMetric
  exact (hG.mul hL.transpose).mul hG

set_option linter.unusedSectionVars false in
/-- A matrix satisfying `L G Lᵀ=G` has the explicit Lorentz inverse on the
right. -/
theorem lorentz_mul_smoothLorentzInverse
    (L : X → Matrix4) (z : X)
    (hLorentz : L z * minkowskiMetric * (L z)ᵀ = minkowskiMetric) :
    L z * smoothLorentzInverse L z = 1 := by
  unfold smoothLorentzInverse
  calc
    L z * (minkowskiMetric * (L z)ᵀ * minkowskiMetric) =
        (L z * minkowskiMetric * (L z)ᵀ) * minkowskiMetric := by
          simp only [Matrix.mul_assoc]
    _ = minkowskiMetric * minkowskiMetric := by rw [hLorentz]
    _ = 1 := minkowskiMetric_sq

/-- The same explicit matrix is also the left inverse. -/
theorem smoothLorentzInverse_mul_lorentz
    (L : X → Matrix4) (z : X)
    (hLorentz : L z * minkowskiMetric * (L z)ᵀ = minkowskiMetric) :
    smoothLorentzInverse L z * L z = 1 := by
  exact mul_eq_one_comm.mp
    (lorentz_mul_smoothLorentzInverse L z hLorentz)

set_option linter.unusedSectionVars false in
/-- The explicit inverse satisfies the metric covariance identity required by
the Maxwell-stress transport theorem. -/
theorem minkowski_mul_transpose_eq_lorentzInverse_mul_minkowski
    (L : X → Matrix4) (z : X) :
    minkowskiMetric * (L z)ᵀ =
      smoothLorentzInverse L z * minkowskiMetric := by
  unfold smoothLorentzInverse
  rw [Matrix.mul_assoc, minkowskiMetric_sq, Matrix.mul_one]

/-- **Smooth local Maxwell-seed theorem.** A smooth frame and positive smooth
magnitude produce a smooth transported real two-form. -/
theorem contDiffOn_smoothTransportedPositiveQSeed
    {n : WithTop ℕ∞} {U : Set X} {L : X → Matrix4} {q : X → ℝ}
    (hL : MatrixFieldContDiffOn n U L) (hqSmooth : ContDiffOn ℝ n q U)
    (hq : ∀ z ∈ U, 0 < q z) :
    MatrixFieldContDiffOn n U (smoothTransportedPositiveQSeed L q) := by
  have hF := contDiffOn_smoothCanonicalPositiveQSeed hqSmooth hq
  change MatrixFieldContDiffOn n U
    (fun z => (L z)ᵀ * smoothCanonicalPositiveQSeed q z * L z)
  exact (hL.transpose.mul hF).mul hL

set_option linter.unusedSectionVars false in
/-- Every field produced by the smooth seed construction is pointwise skew. -/
theorem smoothTransportedPositiveQSeed_transpose
    (L : X → Matrix4) (q : X → ℝ) (z : X) :
    (smoothTransportedPositiveQSeed L q z)ᵀ =
      -smoothTransportedPositiveQSeed L q z := by
  exact transported_seed_transpose (L z) (q z)

set_option linter.unusedSectionVars false in
/-- Under the pointwise Lorentz identities, the smooth local seed has stress
equal to the similarity transport of the canonical residual. -/
theorem smoothTransportedPositiveQSeed_stress
    (L K : X → Matrix4) (q : X → ℝ) (z : X) (hq : 0 < q z)
    (hKL : K z * L z = 1) (hLK : L z * K z = 1)
    (hGLt : minkowskiMetric * (L z)ᵀ = K z * minkowskiMetric)
    (hLGLt : L z * minkowskiMetric * (L z)ᵀ = minkowskiMetric) :
    matrixMaxwellStress minkowskiMetric
        (smoothTransportedPositiveQSeed L q z) =
      transportMixed (K z) (canonicalMaxwellResidual (q z)) (L z) := by
  exact matrixMaxwellStress_transported_seed (L z) (K z) (q z) hq
    hKL hLK hGLt hLGLt

set_option linter.unusedSectionVars false in
/-- **Smooth Lorentz-frame square-root theorem.** The single Lorentz identity
`L G Lᵀ=G` supplies the smooth inverse/coframe and all covariance hypotheses;
the transported smooth seed therefore realizes the transported residual. -/
theorem smoothTransportedPositiveQSeed_stress_of_lorentz
    (L : X → Matrix4) (q : X → ℝ) (z : X) (hq : 0 < q z)
    (hLorentz : L z * minkowskiMetric * (L z)ᵀ = minkowskiMetric) :
    matrixMaxwellStress minkowskiMetric
        (smoothTransportedPositiveQSeed L q z) =
      transportMixed (smoothLorentzInverse L z)
        (canonicalMaxwellResidual (q z)) (L z) := by
  apply smoothTransportedPositiveQSeed_stress L (smoothLorentzInverse L) q z hq
  · exact smoothLorentzInverse_mul_lorentz L z hLorentz
  · exact lorentz_mul_smoothLorentzInverse L z hLorentz
  · exact minkowski_mul_transpose_eq_lorentzInverse_mul_minkowski L z
  · exact hLorentz

end RainichKaluza
