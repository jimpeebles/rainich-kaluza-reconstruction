import RainichKaluza.PhaseIIICurvaturePrincipalData
import RainichKaluza.RankOneEndomorphism

/-!
# Actual scalar contribution from an accepted curvature branch

The curvature branch classifier reconstructs a covector `v=dphi`, while the
Maxwell residual theorem is stated using the mixed scalar contribution

`V^i_j = (1/2) v^i v_j`.

This file closes that representation seam.  A supplied inverse metric raises
the reconstructed covector, the resulting matrix is exactly a basis-free
rank-one endomorphism, and therefore its square coefficient is automatic.
Metric duality and symmetry make it self-adjoint.  These are the two scalar
hypotheses formerly passed independently to the curvature-residual theorem.
In the generic canonical Ricci frame, the same file derives the complete
reconstruction equation from the forced scalar amplitudes and transports that
identity through an arbitrary certified change of frame.
-/

namespace RainichKaluza

open LinearMap (BilinForm)
open scoped Matrix Topology

/-- Canonical generic Ricci endomorphism ordering: the scalar-support
eigenvalues occupy one timelike and one spacelike direction, while `-q,+q`
are the protected Maxwell roots. -/
def canonicalReconstructedRicciMatrix (q a b : ℝ) : Matrix4 :=
  !![a,  0,   0, 0;
      0, -q,   0, 0;
      0,  0,   b, 0;
      0,  0,   0, q]

/-- Canonical embedding of the Lorentzian scalar block in the timelike and
spacelike Ricci eigendirections. -/
noncomputable def canonicalScalarContributionMatrix
    (epsilonA epsilonB x y : ℝ) : Matrix4 :=
  !![scalarMixedDiagonal epsilonA x, 0,
        scalarMixedOffDiagonal epsilonA x y, 0;
      0, 0, 0, 0;
      scalarMixedOffDiagonal epsilonB y x, 0,
        scalarMixedDiagonal epsilonB y, 0;
      0, 0, 0, 0]

/-- **Canonical simple-spectrum reconstruction equation.** The two forced
scalar diagonals solve the full four-dimensional matrix equation; the two
off-diagonal scalar entries lie in the exact `a+b` resonance, and the
protected directions use `q²=qSq`. -/
theorem canonicalScalarContribution_reconstructionEquation
    (q a b qSq epsilonA epsilonB x y : ℝ)
    (hq : q ^ 2 = qSq) (hab : a ≠ b)
    (hx : scalarMixedDiagonal epsilonA x =
      reconstructedDiagonalA a b qSq)
    (hy : scalarMixedDiagonal epsilonB y =
      reconstructedDiagonalB a b qSq) :
    let R := canonicalReconstructedRicciMatrix q a b
    let V := canonicalScalarContributionMatrix epsilonA epsilonB x y
    R * V + V * R - (a + b) • V =
      R * R - qSq • (1 : Matrix4) := by
  have hA := reconstructedDiagonalA_solves a b qSq hab
  have hB := reconstructedDiagonalB_solves a b qSq hab
  dsimp only [canonicalReconstructedRicciMatrix,
    canonicalScalarContributionMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hx, hy] <;>
    nlinarith

/-- The reconstruction equation is covariant under an arbitrary two-sided
similarity transform. -/
theorem reconstructionEquation_transportMixed
    (R V K L : Matrix4) (traceV qSq : ℝ)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (h : R * V + V * R - traceV • V =
      R * R - qSq • (1 : Matrix4)) :
    let R' := transportMixed K R L
    let V' := transportMixed K V L
    R' * V' + V' * R' - traceV • V' =
      R' * R' - qSq • (1 : Matrix4) := by
  dsimp only [transportMixed]
  simp only [Algebra.smul_def] at h ⊢
  have hprod (A B : Matrix4) :
      (K * A * L) * (K * B * L) = K * (A * B) * L := by
    calc
      (K * A * L) * (K * B * L) = K * A * (L * K) * B * L := by
        noncomm_ring
      _ = K * (A * B) * L := by rw [hLK]; simp; noncomm_ring
  have hscalar (c : ℝ) (A : Matrix4) :
      algebraMap ℝ Matrix4 c * (K * A * L) =
        K * (algebraMap ℝ Matrix4 c * A) * L := by
    have hcK := Algebra.commutes c K
    calc
      algebraMap ℝ Matrix4 c * (K * A * L) =
          (algebraMap ℝ Matrix4 c * K) * A * L := by noncomm_ring
      _ = (K * algebraMap ℝ Matrix4 c) * A * L := by rw [hcK]
      _ = K * (algebraMap ℝ Matrix4 c * A) * L := by noncomm_ring
  have hscalarOne (c : ℝ) :
      K * (algebraMap ℝ Matrix4 c * 1) * L =
        algebraMap ℝ Matrix4 c * 1 := by
    have hcK := Algebra.commutes c K
    calc
      K * (algebraMap ℝ Matrix4 c * 1) * L =
          (K * algebraMap ℝ Matrix4 c) * L := by simp
      _ = (algebraMap ℝ Matrix4 c * K) * L := by rw [hcK]
      _ = algebraMap ℝ Matrix4 c * (K * L) := by noncomm_ring
      _ = algebraMap ℝ Matrix4 c * 1 := by rw [hKL]
  calc
    (K * R * L) * (K * V * L) + (K * V * L) * (K * R * L) -
        algebraMap ℝ Matrix4 traceV * (K * V * L) =
      K * (R * V + V * R - algebraMap ℝ Matrix4 traceV * V) * L := by
        rw [hprod R V, hprod V R, hscalar traceV V]
        noncomm_ring
    _ = K * (R * R - algebraMap ℝ Matrix4 qSq * 1) * L := by rw [h]
    _ = (K * R * L) * (K * R * L) -
        algebraMap ℝ Matrix4 qSq * 1 := by
      rw [mul_sub, sub_mul, hprod R R, hscalarOne qSq]

/-- Canonical reconstruction therefore holds in every supplied frame whose
forward and inverse matrices are certified. -/
theorem transportedCanonicalScalarContribution_reconstructionEquation
    (q a b qSq epsilonA epsilonB x y : ℝ)
    (K L : Matrix4) (hKL : K * L = 1) (hLK : L * K = 1)
    (hq : q ^ 2 = qSq) (hab : a ≠ b)
    (hx : scalarMixedDiagonal epsilonA x =
      reconstructedDiagonalA a b qSq)
    (hy : scalarMixedDiagonal epsilonB y =
      reconstructedDiagonalB a b qSq) :
    let R := transportMixed K (canonicalReconstructedRicciMatrix q a b) L
    let V := transportMixed K
      (canonicalScalarContributionMatrix epsilonA epsilonB x y) L
    R * V + V * R - (a + b) • V =
      R * R - qSq • (1 : Matrix4) := by
  exact reconstructionEquation_transportMixed
    (canonicalReconstructedRicciMatrix q a b)
    (canonicalScalarContributionMatrix epsilonA epsilonB x y)
    K L (a + b) qSq hKL hLK
    (canonicalScalarContribution_reconstructionEquation
      q a b qSq epsilonA epsilonB x y hq hab hx hy)

/-- Vector obtained by raising a coordinate covector with an inverse metric
matrix. -/
def scalarRaisedVector
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    CurvatureCoordinateSpace4 :=
  (gInv z).mulVec (v z)

/-- Actual mixed scalar contribution
`V^i_j=(1/2) g^{ik}v_k v_j`. -/
noncomputable def scalarContributionMatrixField
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    Matrix4 :=
  fun i j => ((2 : ℝ)⁻¹ * v z j) * scalarRaisedVector gInv v z i

/-- The scalar multiplying the rank-one square law; in finite dimension this
is also the mixed trace `tr V = (1/2) v(v sharp)`. -/
noncomputable def scalarContributionTraceField
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) : ℝ :=
  oneForm4Evaluate (v z)
    ((2 : ℝ)⁻¹ • scalarRaisedVector gInv v z)

/-- Matrix realization of the scalar contribution is exactly the basis-free
rank-one endomorphism built from the half-covector and its metric dual. -/
theorem scalarContributionMatrixField_toLin'
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    Matrix.toLin' (scalarContributionMatrixField gInv v z) =
      rankOneEndomorphism
        (oneForm4ContinuousLinearMap (v z)).toLinearMap
        ((2 : ℝ)⁻¹ • scalarRaisedVector gInv v z) := by
  apply LinearMap.ext
  intro y
  apply funext
  intro i
  rw [Matrix.toLin'_apply]
  change
    (∑ j, (((2 : ℝ)⁻¹ * v z j) *
      scalarRaisedVector gInv v z i) * y j) =
      oneForm4Evaluate (v z) y *
        ((2 : ℝ)⁻¹ * scalarRaisedVector gInv v z i)
  unfold oneForm4Evaluate
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Automatic scalar square law.** No independent rank-one or trace
hypothesis is required once `V` is constructed from the branch covector. -/
theorem scalarContributionMatrixField_sq
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    scalarContributionMatrixField gInv v z *
        scalarContributionMatrixField gInv v z =
      scalarContributionTraceField gInv v z •
        scalarContributionMatrixField gInv v z := by
  ext i j
  rw [Matrix.mul_apply]
  unfold scalarContributionMatrixField scalarContributionTraceField
    oneForm4Evaluate
  change
    (∑ k, (((2 : ℝ)⁻¹ * v z k) *
        scalarRaisedVector gInv v z i) *
      (((2 : ℝ)⁻¹ * v z j) *
        scalarRaisedVector gInv v z k)) =
      (∑ k, v z k *
        ((2 : ℝ)⁻¹ * scalarRaisedVector gInv v z k)) *
      (((2 : ℝ)⁻¹ * v z j) * scalarRaisedVector gInv v z i)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A rank-one map constructed from a covector and its metric-dual vector is
self-adjoint for a symmetric bilinear form. -/
theorem rankOneEndomorphism_metricSelfAdjoint_of_dual
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (f : V →ₗ[ℝ] ℝ) (x : V) (c : ℝ)
    (hdual : ∀ y, g x y = c * f y) :
    MetricSelfAdjoint g (rankOneEndomorphism f x) := by
  intro y z
  simp only [rankOneEndomorphism_apply, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [hdual z, hg.eq y x, hdual y]
  ring

/-- The constructed scalar mixed tensor is metric self-adjoint whenever the
supplied inverse metric really raises the selected half-covector. -/
theorem scalarContributionMatrixField_metricSelfAdjoint
    {X : Type*} (g : X → BilinForm ℝ CurvatureCoordinateSpace4)
    (gInv : X → Matrix4) (v : X → OneForm4) (z : X)
    (hgsymm : (g z).IsSymm)
    (hdual : ∀ y,
      g z (scalarRaisedVector gInv v z) y =
        oneForm4Evaluate (v z) y) :
    MetricSelfAdjoint (g z)
      (Matrix.toLin' (scalarContributionMatrixField gInv v z)) := by
  rw [scalarContributionMatrixField_toLin']
  apply rankOneEndomorphism_metricSelfAdjoint_of_dual
    (g z) hgsymm _ _ (2 : ℝ)⁻¹
  intro y
  simp only [LinearMap.BilinForm.smul_left, hdual y]
  congr 1

/-- Entrywise smooth inverse metric and covector fields produce an entrywise
smooth scalar-contribution matrix field. -/
theorem contDiffOn_scalarContributionMatrixField
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X}
    {gInv : X → Matrix4} {v : X → OneForm4}
    (hgInv : MatrixFieldContDiffOn n U gInv)
    (hv : ∀ j, ContDiffOn ℝ n (fun z => v z j) U) :
    MatrixFieldContDiffOn n U
      (scalarContributionMatrixField gInv v) := by
  intro i j
  have hraised : ContDiffOn ℝ n
      (fun z => scalarRaisedVector gInv v z i) U := by
    simpa only [scalarRaisedVector, Matrix.mulVec, dotProduct] using
      (ContDiffOn.sum fun k _ => (hgInv i k).mul (hv k))
  exact (contDiffOn_const.mul (hv j)).mul hraised

/-- A two-sided inverse of a symmetric matrix is itself symmetric. -/
theorem inverseMatrix_transpose_eq_self_of_symmetric
    (g gInv : Matrix4) (hg : gᵀ = g)
    (hright : g * gInv = 1) :
    gInvᵀ = gInv := by
  have ht : gInvᵀ * g = 1 := by
    have h := congrArg Matrix.transpose hright
    simpa only [Matrix.transpose_mul, Matrix.transpose_one, hg] using h
  calc
    gInvᵀ = gInvᵀ * 1 := by rw [Matrix.mul_one]
    _ = gInvᵀ * (g * gInv) := by rw [hright]
    _ = (gInvᵀ * g) * gInv := by rw [Matrix.mul_assoc]
    _ = 1 * gInv := by rw [ht]
    _ = gInv := Matrix.one_mul _

/-- Matrix inversion really raises the covector: the inverse-metric `mulVec`
is dual to the original covector for the bilinear form represented by `g`. -/
theorem scalarRaisedVector_isMetricDual
    (g gInv : Matrix4) (v y : OneForm4)
    (hgInv : gInvᵀ = gInv) (hinv : gInv * g = 1) :
    Matrix.toBilin' g (gInv.mulVec v) y = oneForm4Evaluate v y := by
  rw [Matrix.toBilin'_apply', dotProduct_comm]
  rw [← Matrix.dotProduct_transpose_mulVec gInv v (g.mulVec y)]
  rw [hgInv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rfl

/-- Consequently a symmetric metric matrix and its two-sided inverse make the
constructed scalar contribution self-adjoint with no independent duality
hypothesis. -/
theorem scalarContributionMatrixField_metricSelfAdjoint_of_inverse
    {X : Type*} (g gInv : X → Matrix4) (v : X → OneForm4) (z : X)
    (hg : (g z)ᵀ = g z)
    (hleft : gInv z * g z = 1) (hright : g z * gInv z = 1) :
    MetricSelfAdjoint (Matrix.toBilin' (g z))
      (Matrix.toLin' (scalarContributionMatrixField gInv v z)) := by
  have hgsymm : (Matrix.toBilin' (g z)).IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr hg
  apply scalarContributionMatrixField_metricSelfAdjoint
    (fun z => Matrix.toBilin' (g z)) gInv v z hgsymm
  intro y
  exact scalarRaisedVector_isMetricDual (g z) (gInv z) (v z) y
    (inverseMatrix_transpose_eq_self_of_symmetric
      (g z) (gInv z) hg hright) hleft

/-- Scalar mixed tensor selected by one of the two concrete curvature
branches. -/
noncomputable def CurvatureScalarBranchComponentPatch4.scalarContribution
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  scalarContributionMatrixField gInv
    (C.branchScalarOneFormValue branch) z

/-- The actual branch scalar contribution obeys the required square law
identically. -/
theorem CurvatureScalarBranchComponentPatch4.scalarContribution_sq
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4) :
    C.scalarContribution gInv branch z *
        C.scalarContribution gInv branch z =
      scalarContributionTraceField gInv
          (C.branchScalarOneFormValue branch) z •
        C.scalarContribution gInv branch z := by
  exact scalarContributionMatrixField_sq gInv
    (C.branchScalarOneFormValue branch) z

/-- Smooth branch covector components and inverse metric give the precise
smooth scalar-contribution field consumed by the residual constructor. -/
theorem CurvatureScalarBranchComponentPatch4.contDiffOn_scalarContribution
    {U : Set CurvatureCoordinateSpace4}
    {n : WithTop ℕ∞}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (branch : RelativeSignScalarBranch4)
    (hgInv : MatrixFieldContDiffOn n U gInv)
    (hv : ∀ j, ContDiffOn ℝ n
      (fun z => C.branchScalarOneFormValue branch z j) U) :
    MatrixFieldContDiffOn n U
      (C.scalarContribution gInv branch) := by
  exact contDiffOn_scalarContributionMatrixField hgInv hv

/-- The actual branch scalar contribution is self-adjoint once the supplied
inverse metric is certified to raise that branch covector. -/
theorem CurvatureScalarBranchComponentPatch4.scalarContribution_metricSelfAdjoint
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (g : CurvatureCoordinateSpace4 →
      BilinForm ℝ CurvatureCoordinateSpace4)
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (g z).IsSymm)
    (hdual : ∀ y,
      g z (scalarRaisedVector gInv
        (C.branchScalarOneFormValue branch) z) y =
        oneForm4Evaluate (C.branchScalarOneFormValue branch z) y) :
    MetricSelfAdjoint (g z)
      (Matrix.toLin' (C.scalarContribution gInv branch z)) := by
  exact scalarContributionMatrixField_metricSelfAdjoint g gInv
    (C.branchScalarOneFormValue branch) z hgsymm hdual

/-- The concrete branch contribution is self-adjoint directly from a
symmetric metric matrix and its certified two-sided inverse. -/
theorem CurvatureScalarBranchComponentPatch4.scalarContribution_metricSelfAdjoint_of_inverse
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (g gInv : CurvatureCoordinateSpace4 → Matrix4)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4)
    (hg : (g z)ᵀ = g z)
    (hleft : gInv z * g z = 1) (hright : g z * gInv z = 1) :
    MetricSelfAdjoint (Matrix.toBilin' (g z))
      (Matrix.toLin' (C.scalarContribution gInv branch z)) := by
  exact scalarContributionMatrixField_metricSelfAdjoint_of_inverse
    g gInv (C.branchScalarOneFormValue branch) z hg hleft hright

/-- The accepted branch's actual Maxwell residual is self-adjoint once the
mixed Ricci field is self-adjoint and the metric inverse is certified. -/
theorem curvatureMaxwellResidualField_metricSelfAdjoint_of_branchScalarContribution
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (g R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4)
    (hg : (g z)ᵀ = g z)
    (hleft : gInv z * g z = 1) (hright : g z * gInv z = 1)
    (hR : MetricSelfAdjoint (Matrix.toBilin' (g z))
      (Matrix.toLin' (R z))) :
    MetricSelfAdjoint (Matrix.toBilin' (g z))
      (Matrix.toLin'
        (curvatureMaxwellResidualField R
          (C.scalarContribution gInv branch) z)) := by
  exact curvatureMaxwellResidualField_metricSelfAdjoint
    (Matrix.toBilin' (g z)) R (C.scalarContribution gInv branch) z hR
    (C.scalarContribution_metricSelfAdjoint_of_inverse
      g gInv branch z hg hleft hright)

/-- **Accepted-branch residual square theorem.** For the scalar contribution
actually constructed from the selected curvature covector, the Maxwell square
law follows from the reconstruction equation alone; the scalar square law is
no longer a separate hypothesis. -/
theorem curvatureMaxwellResidualField_sq_of_branchScalarContribution
    {U : Set CurvatureCoordinateSpace4}
    (C : CurvatureScalarBranchComponentPatch4 U)
    (R gInv : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (branch : RelativeSignScalarBranch4)
    (z : CurvatureCoordinateSpace4)
    (hrecon :
      R z * C.scalarContribution gInv branch z +
          C.scalarContribution gInv branch z * R z -
          scalarContributionTraceField gInv
            (C.branchScalarOneFormValue branch) z •
              C.scalarContribution gInv branch z =
        R z * R z - qSq z • (1 : Matrix4)) :
    curvatureMaxwellResidualField R
          (C.scalarContribution gInv branch) z *
        curvatureMaxwellResidualField R
          (C.scalarContribution gInv branch) z =
      qSq z • (1 : Matrix4) := by
  exact curvatureMaxwellResidualField_sq R
    (C.scalarContribution gInv branch)
    (scalarContributionTraceField gInv
      (C.branchScalarOneFormValue branch)) qSq z
    (C.scalarContribution_sq gInv branch z) hrecon

end RainichKaluza
