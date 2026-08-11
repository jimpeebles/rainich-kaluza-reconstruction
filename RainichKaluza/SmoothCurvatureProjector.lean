import RainichKaluza.SpectralProjectorDerivative
import RainichKaluza.ScalarAmplitudeDerivative
import RainichKaluza.SmoothMaxwellSeed
import RainichKaluza.LocalExteriorSeed
import RainichKaluza.CoordinateRicci
import RainichKaluza.DifferentialBranchSelection
import Mathlib.Tactic.Module

/-!
# Smooth curvature projectors and scalar branch forms

This file closes the coordinate-local geometric interface between the
evaluated spectral algebra and the Phase-II differential branch test.

First, the four-root Lagrange polynomial is realized as an entrywise smooth
matrix field on every simple-spectrum patch.  Fixed probes projected by these
curvature-polynomial fields are smooth, so the existing strict-sign
normalizations produce smooth eigenline fields and metric-dual one-forms.

Second, the evaluated spectral-projector derivative theorem is specialized to
the coordinate Levi--Civita derivative of a mixed tensor.  This makes the
dependence of `∇P` on `∇R` and the three spectral gaps explicit in a genuine
four-coordinate jet.

Finally, the two scalar spectral components `alpha` and `beta` are assembled
from their curvature-reconstructed amplitudes and eigen-one-forms.  Their
coordinate first jets and exterior derivatives are explicit product-rule
formulas.  The sum/difference branches exteriorize to `dalpha ± dbeta`, so the
already proved relative-sign classifier applies without an abstract
differential placeholder.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section SmoothMatrixProjectors

/-- Entrywise smooth matrix fields are closed under addition. -/
theorem MatrixFieldContDiffOn.add
    {n : WithTop ℕ∞} {U : Set X} {A B : X → Matrix4}
    (hA : MatrixFieldContDiffOn n U A)
    (hB : MatrixFieldContDiffOn n U B) :
    MatrixFieldContDiffOn n U (fun z => A z + B z) := by
  intro i j
  exact (hA i j).add (hB i j)

/-- Entrywise smooth matrix fields are closed under subtraction. -/
theorem MatrixFieldContDiffOn.sub
    {n : WithTop ℕ∞} {U : Set X} {A B : X → Matrix4}
    (hA : MatrixFieldContDiffOn n U A)
    (hB : MatrixFieldContDiffOn n U B) :
    MatrixFieldContDiffOn n U (fun z => A z - B z) := by
  intro i j
  exact (hA i j).sub (hB i j)

/-- A smooth scalar field times a smooth matrix field is entrywise smooth. -/
theorem MatrixFieldContDiffOn.smulField
    {n : WithTop ℕ∞} {U : Set X} {c : X → ℝ} {A : X → Matrix4}
    (hc : ContDiffOn ℝ n c U)
    (hA : MatrixFieldContDiffOn n U A) :
    MatrixFieldContDiffOn n U (fun z => c z • A z) := by
  intro i j
  simpa only [Matrix.smul_apply, smul_eq_mul] using hc.mul (hA i j)

/-- The matrix factor `R-rI` used in the coordinate Lagrange polynomial. -/
def matrixEigenFactorField
    (R : X → Matrix4) (r : X → ℝ) (z : X) : Matrix4 :=
  R z - r z • (1 : Matrix4)

/-- A smooth Ricci matrix and smooth root give a smooth linear factor. -/
theorem contDiffOn_matrixEigenFactorField
    {n : WithTop ℕ∞} {U : Set X} {R : X → Matrix4} {r : X → ℝ}
    (hR : MatrixFieldContDiffOn n U R)
    (hr : ContDiffOn ℝ n r U) :
    MatrixFieldContDiffOn n U (matrixEigenFactorField R r) := by
  apply hR.sub
  exact MatrixFieldContDiffOn.smulField hr
    (matrixFieldContDiffOn_const (1 : Matrix4))

/-- Coordinate-matrix realization of the four-root Lagrange projector. -/
noncomputable def matrixFourRootProjectorField
    (R : X → Matrix4) (a b c d : X → ℝ) (z : X) : Matrix4 :=
  (((a z - b z) * (a z - c z) * (a z - d z))⁻¹) •
    ((matrixEigenFactorField R b z * matrixEigenFactorField R c z) *
      matrixEigenFactorField R d z)

/-- **Smooth curvature-projector theorem.** The Lagrange projector is a
genuine smooth matrix field wherever its three target spectral gaps do not
vanish. -/
theorem contDiffOn_matrixFourRootProjectorField
    {n : WithTop ℕ∞} {U : Set X}
    {R : X → Matrix4} {a b c d : X → ℝ}
    (hR : MatrixFieldContDiffOn n U R)
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U)
    (hc : ContDiffOn ℝ n c U) (hd : ContDiffOn ℝ n d U)
    (hgap : ∀ z ∈ U,
      (a z - b z) * (a z - c z) * (a z - d z) ≠ 0) :
    MatrixFieldContDiffOn n U
      (matrixFourRootProjectorField R a b c d) := by
  have hden : ContDiffOn ℝ n
      (fun z => (a z - b z) * (a z - c z) * (a z - d z)) U :=
    ((ha.sub hb).mul (ha.sub hc)).mul (ha.sub hd)
  have hinv : ContDiffOn ℝ n
      (fun z => ((a z - b z) * (a z - c z) * (a z - d z))⁻¹) U :=
    hden.inv hgap
  have hB := contDiffOn_matrixEigenFactorField hR hb
  have hC := contDiffOn_matrixEigenFactorField hR hc
  have hD := contDiffOn_matrixEigenFactorField hR hd
  exact MatrixFieldContDiffOn.smulField hinv ((hB.mul hC).mul hD)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The coordinate matrix polynomial is exactly the basis matrix of the
basis-free Lagrange projector already used by the spectral algebra. -/
theorem matrixFourRootProjectorField_toLin'
    (R : X → Matrix4) (a b c d : X → ℝ) (z : X) :
    Matrix.toLin' (matrixFourRootProjectorField R a b c d z) =
      fourRootProjector (Matrix.toLin' (R z))
        (a z) (b z) (c z) (d z) := by
  simp only [matrixFourRootProjectorField, fourRootProjector,
    matrixEigenFactorField, eigenFactor, map_smul, map_sub,
    Matrix.toLin'_one, Matrix.toLin'_mul, Module.End.mul_eq_comp,
    Module.End.one_eq_id]

/-- Coordinate version of the four-eigenspace decomposition hypothesis. -/
def MatrixHasFourEigenspaceDecomposition
    (R : Matrix4) (a b c d : ℝ) : Prop :=
  HasFourEigenspaceDecomposition (Matrix.toLin' R) a b c d

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Every smooth Lagrange field is pointwise idempotent under the explicit
simple-spectrum decomposition hypothesis. -/
theorem matrixFourRootProjectorField_sq
    (R : X → Matrix4) (a b c d : X → ℝ) (z : X)
    (hab : a z ≠ b z) (hac : a z ≠ c z) (had : a z ≠ d z)
    (hdecomp : MatrixHasFourEigenspaceDecomposition
      (R z) (a z) (b z) (c z) (d z)) :
    matrixFourRootProjectorField R a b c d z *
        matrixFourRootProjectorField R a b c d z =
      matrixFourRootProjectorField R a b c d z := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  simp only [matrixFourRootProjectorField_toLin']
  exact fourRootProjector_sq (Matrix.toLin' (R z))
    (a z) (b z) (c z) (d z) hab hac had hdecomp

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The four smooth coordinate Lagrange fields resolve the identity
pointwise on a simple-spectrum decomposition. -/
theorem matrixFourRootProjectorFields_sum_eq_one
    (R : X → Matrix4) (a b c d : X → ℝ) (z : X)
    (hab : a z ≠ b z) (hac : a z ≠ c z) (had : a z ≠ d z)
    (hbc : b z ≠ c z) (hbd : b z ≠ d z) (hcd : c z ≠ d z)
    (hdecomp : MatrixHasFourEigenspaceDecomposition
      (R z) (a z) (b z) (c z) (d z)) :
    matrixFourRootProjectorField R a b c d z +
        matrixFourRootProjectorField R b a c d z +
        matrixFourRootProjectorField R c a b d z +
        matrixFourRootProjectorField R d a b c z = 1 := by
  apply Matrix.toLin'.injective
  simp only [map_add, matrixFourRootProjectorField_toLin',
    Matrix.toLin'_one]
  exact fourRootProjectors_sum_eq_one (Matrix.toLin' (R z))
    (a z) (b z) (c z) (d z) hab hac had hbc hbd hcd hdecomp

/-- A fixed vector projected by a smooth matrix field. -/
def smoothMatrixProjectedVector
    (P : X → Matrix4) (u : Fin 4 → ℝ) (z : X) : Fin 4 → ℝ :=
  P z *ᵥ u

/-- Fixed probes become smooth coordinate vector fields after application of
an entrywise smooth curvature projector. -/
theorem contDiffOn_smoothMatrixProjectedVector
    {n : WithTop ℕ∞} {U : Set X} {P : X → Matrix4}
    (hP : MatrixFieldContDiffOn n U P) (u : Fin 4 → ℝ) :
    ContDiffOn ℝ n (smoothMatrixProjectedVector P u) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ => (hP i j).mul contDiffOn_const

/-- Metric dual of a varying vector field in a normed local
trivialization. -/
noncomputable def smoothMetricDualCovector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : X → ContinuousBilinForm V) (v : X → V) (z : X) : V →L[ℝ] ℝ :=
  g z (v z)

/-- Smooth metric and vector fields give a smooth metric-dual covector
field. -/
theorem contDiffOn_smoothMetricDualCovector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {v : X → V}
    (hg : ContDiffOn ℝ n g U) (hv : ContDiffOn ℝ n v U) :
    ContDiffOn ℝ n (smoothMetricDualCovector g v) U := by
  exact hg.clm_apply hv

/-- Metric-dual eigen-one-form obtained from a timelike normalized fixed
probe in a curvature-projector range. -/
noncomputable def smoothTimelikeCurvatureEigenCovector
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (u : Fin 4 → ℝ) (z : X) :
    (Fin 4 → ℝ) →L[ℝ] ℝ :=
  smoothMetricDualCovector g
    (smoothNormalizeTimelike g (smoothMatrixProjectedVector P u)) z

/-- The timelike curvature eigen-one-form is smooth on its strict-sign
fixed-probe patch. -/
theorem contDiffOn_smoothTimelikeCurvatureEigenCovector
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm (Fin 4 → ℝ)}
    {P : X → Matrix4} (u : Fin 4 → ℝ)
    (hg : ContDiffOn ℝ n g U) (hP : MatrixFieldContDiffOn n U P)
    (htime : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector P u)
      (smoothMatrixProjectedVector P u) z < 0) :
    ContDiffOn ℝ n (smoothTimelikeCurvatureEigenCovector g P u) U := by
  have hprobe := contDiffOn_smoothMatrixProjectedVector hP u
  have hnormalized := contDiffOn_smoothNormalizeTimelike hg hprobe htime
  exact contDiffOn_smoothMetricDualCovector hg hnormalized

/-- Metric-dual eigen-one-form obtained from a spacelike normalized fixed
probe in a curvature-projector range. -/
noncomputable def smoothSpacelikeCurvatureEigenCovector
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (u : Fin 4 → ℝ) (z : X) :
    (Fin 4 → ℝ) →L[ℝ] ℝ :=
  smoothMetricDualCovector g
    (smoothNormalizeSpacelike g (smoothMatrixProjectedVector P u)) z

/-- The spacelike curvature eigen-one-form is smooth on its strict-sign
fixed-probe patch. -/
theorem contDiffOn_smoothSpacelikeCurvatureEigenCovector
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm (Fin 4 → ℝ)}
    {P : X → Matrix4} (u : Fin 4 → ℝ)
    (hg : ContDiffOn ℝ n g U) (hP : MatrixFieldContDiffOn n U P)
    (hspace : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector P u)
      (smoothMatrixProjectedVector P u) z) :
    ContDiffOn ℝ n (smoothSpacelikeCurvatureEigenCovector g P u) U := by
  have hprobe := contDiffOn_smoothMatrixProjectedVector hP u
  have hnormalized := contDiffOn_smoothNormalizeSpacelike hg hprobe hspace
  exact contDiffOn_smoothMetricDualCovector hg hnormalized

/-- Pointwise positive amplitude selected from a signature-adjusted scalar
diagonal `u`: `x=sqrt(2 epsilon u)`. -/
noncomputable def smoothScalarAmplitude
    (epsilon : ℝ) (u : X → ℝ) (z : X) : ℝ :=
  Real.sqrt (2 * epsilon * u z)

/-- The selected scalar amplitude is smooth wherever the
signature-adjusted diagonal is strictly positive. -/
theorem contDiffOn_smoothScalarAmplitude
    {n : WithTop ℕ∞} {U : Set X} (epsilon : ℝ) {u : X → ℝ}
    (hu : ContDiffOn ℝ n u U)
    (hpos : ∀ z ∈ U, 0 < 2 * epsilon * u z) :
    ContDiffOn ℝ n (smoothScalarAmplitude epsilon u) U := by
  have harg : ContDiffOn ℝ n (fun z => 2 * epsilon * u z) U :=
    contDiffOn_const.mul hu
  exact harg.sqrt (fun z hz => ne_of_gt (hpos z hz))

/-- The forced first scalar diagonal is smooth on the noncolliding root
patch. -/
theorem contDiffOn_reconstructedDiagonalA
    {n : WithTop ℕ∞} {U : Set X} {a b qSq : X → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U)
    (hqSq : ContDiffOn ℝ n qSq U)
    (hab : ∀ z ∈ U, a z ≠ b z) :
    ContDiffOn ℝ n
      (fun z => reconstructedDiagonalA (a z) (b z) (qSq z)) U := by
  unfold reconstructedDiagonalA
  exact ((ha.pow 2).sub hqSq).div (ha.sub hb)
    (fun z hz => sub_ne_zero.mpr (hab z hz))

/-- The forced second scalar diagonal is smooth on the noncolliding root
patch. -/
theorem contDiffOn_reconstructedDiagonalB
    {n : WithTop ℕ∞} {U : Set X} {a b qSq : X → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U)
    (hqSq : ContDiffOn ℝ n qSq U)
    (hab : ∀ z ∈ U, a z ≠ b z) :
    ContDiffOn ℝ n
      (fun z => reconstructedDiagonalB (a z) (b z) (qSq z)) U := by
  unfold reconstructedDiagonalB
  exact ((hb.pow 2).sub hqSq).div (hb.sub ha)
    (fun z hz => sub_ne_zero.mpr (hab z hz).symm)

/-- Scalar amplitude times a spectral eigen-one-form. -/
def smoothSpectralComponent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : X → ℝ) (theta : X → V →L[ℝ] ℝ) (z : X) : V →L[ℝ] ℝ :=
  x z • theta z

/-- Smooth amplitudes and smooth eigen-one-forms assemble to smooth scalar
spectral components `alpha` and `beta`. -/
theorem contDiffOn_smoothSpectralComponent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {U : Set X}
    {x : X → ℝ} {theta : X → V →L[ℝ] ℝ}
    (hx : ContDiffOn ℝ n x U) (htheta : ContDiffOn ℝ n theta U) :
    ContDiffOn ℝ n (smoothSpectralComponent x theta) U := by
  exact hx.smul htheta

end SmoothMatrixProjectors

section LeviCivitaProjectorJet

/-- Coordinate matrix of the connection action in derivative direction
`k`: `(Gamma_k)^i_j = Gamma^i_{k j}`. -/
def coordinateConnectionMatrix
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ) (k : Fin 4) : Matrix4 :=
  fun i j => Gamma i k j

/-- Coordinate covariant derivative of a mixed `(1,1)` tensor.  The formula
is `nabla_k T = partial_k T + Gamma_k T - T Gamma_k`. -/
noncomputable def mixedTensorCovariantDerivative
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Matrix4) (dT : Fin 4 → Matrix4) (k : Fin 4) : Matrix4 :=
  dT k + coordinateConnectionMatrix Gamma k * T -
    T * coordinateConnectionMatrix Gamma k

/-- The mixed-tensor connection is a derivation: a raw coordinate product
rule becomes the covariant product rule after the two connection actions
cancel. -/
theorem mixedTensorCovariantDerivative_mul
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T U : Matrix4) (dT dU dTU : Fin 4 → Matrix4) (k : Fin 4)
    (hraw : dTU k = dT k * U + T * dU k) :
    mixedTensorCovariantDerivative Gamma (T * U) dTU k =
      mixedTensorCovariantDerivative Gamma T dT k * U +
        T * mixedTensorCovariantDerivative Gamma U dU k := by
  unfold mixedTensorCovariantDerivative
  rw [hraw]
  noncomm_ring

/-- Scalar multiplication has the expected covariant product rule because
the connection acts only on tensor indices. -/
theorem mixedTensorCovariantDerivative_smul
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (a : ℝ) (da : OneForm4) (p : Matrix4)
    (dp : Fin 4 → Matrix4) (k : Fin 4) :
    mixedTensorCovariantDerivative Gamma (a • p)
        (fun l => da l • p + a • dp l) k =
      da k • p + a • mixedTensorCovariantDerivative Gamma p dp k := by
  unfold mixedTensorCovariantDerivative
  rw [mul_smul_comm, smul_mul_assoc]
  module

/-- Differentiating idempotence in coordinates gives the corresponding
covariant identity automatically. -/
theorem mixedTensorCovariantDerivative_idempotent
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (p : Matrix4) (dp : Fin 4 → Matrix4) (k : Fin 4)
    (hp : p * p = p)
    (hraw : ∀ l, dp l * p + p * dp l = dp l) :
    mixedTensorCovariantDerivative Gamma p dp k * p +
        p * mixedTensorCovariantDerivative Gamma p dp k =
      mixedTensorCovariantDerivative Gamma p dp k := by
  have hmul := mixedTensorCovariantDerivative_mul Gamma p p dp dp
    (fun l => dp l * p + p * dp l) k rfl
  simpa only [hp, hraw] using hmul.symm

/-- A differentiated left eigen-equation in coordinate partial derivatives
is the same differentiated eigen-equation for the mixed-tensor covariant
derivative. -/
theorem mixedTensorCovariantDerivative_eigen_left
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R p : Matrix4) (dR dp : Fin 4 → Matrix4)
    (a : ℝ) (da : OneForm4) (k : Fin 4)
    (hRp : R * p = a • p)
    (hraw : ∀ l, dR l * p + R * dp l = da l • p + a • dp l) :
    mixedTensorCovariantDerivative Gamma R dR k * p +
        R * mixedTensorCovariantDerivative Gamma p dp k =
      da k • p + a • mixedTensorCovariantDerivative Gamma p dp k := by
  have hmul := mixedTensorCovariantDerivative_mul Gamma R p dR dp
    (fun l => dR l * p + R * dp l) k rfl
  have hscalar := mixedTensorCovariantDerivative_smul Gamma a da p dp k
  calc
    mixedTensorCovariantDerivative Gamma R dR k * p +
          R * mixedTensorCovariantDerivative Gamma p dp k =
        mixedTensorCovariantDerivative Gamma (R * p)
          (fun l => dR l * p + R * dp l) k := hmul.symm
    _ = mixedTensorCovariantDerivative Gamma (a • p)
          (fun l => da l • p + a • dp l) k := by
      congr 1
      · funext l
        exact hraw l
    _ = da k • p + a • mixedTensorCovariantDerivative Gamma p dp k :=
      hscalar

/-- Right-eigen version of the coordinate-to-covariant differentiated
spectral identity. -/
theorem mixedTensorCovariantDerivative_eigen_right
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R p : Matrix4) (dR dp : Fin 4 → Matrix4)
    (a : ℝ) (da : OneForm4) (k : Fin 4)
    (hpR : p * R = a • p)
    (hraw : ∀ l, dp l * R + p * dR l = da l • p + a • dp l) :
    mixedTensorCovariantDerivative Gamma p dp k * R +
        p * mixedTensorCovariantDerivative Gamma R dR k =
      da k • p + a • mixedTensorCovariantDerivative Gamma p dp k := by
  have hmul := mixedTensorCovariantDerivative_mul Gamma p R dp dR
    (fun l => dp l * R + p * dR l) k rfl
  have hscalar := mixedTensorCovariantDerivative_smul Gamma a da p dp k
  calc
    mixedTensorCovariantDerivative Gamma p dp k * R +
          p * mixedTensorCovariantDerivative Gamma R dR k =
        mixedTensorCovariantDerivative Gamma (p * R)
          (fun l => dp l * R + p * dR l) k := hmul.symm
    _ = mixedTensorCovariantDerivative Gamma (a • p)
          (fun l => da l • p + a • dp l) k := by
      congr 1
      · funext l
        exact hraw l
    _ = da k • p + a • mixedTensorCovariantDerivative Gamma p dp k :=
      hscalar

/-- Levi--Civita specialization using the Christoffel symbols determined by a
metric inverse and symmetric first metric jet. -/
noncomputable def leviCivitaMixedTensorDerivative
    (gInv : Matrix4) (dg : CoordinateMetricJet1 (Fin 4))
    (T : Matrix4) (dT : Fin 4 → Matrix4) (k : Fin 4) : Matrix4 :=
  mixedTensorCovariantDerivative
    (coordinateChristoffel gInv dg) T dT k

/-- **Levi--Civita four-block projector derivative.** For every coordinate
direction, the derivative of a simple Ricci projector is reconstructed from
the Levi--Civita derivative of the Ricci endomorphism and the three spectral
gaps.  The assumptions are precisely the pointwise spectral identities and
their covariant derivatives. -/
theorem leviCivitaSpectralProjectorDerivative_fourBlock
    (gInv : Matrix4) (dg : CoordinateMetricJet1 (Fin 4))
    (R : Matrix4) (dR : Fin 4 → Matrix4)
    (p : Matrix4) (dp : Fin 4 → Matrix4)
    (q r s : Matrix4) (a b c d : ℝ) (da : OneForm4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hp : p * p = p) (hsum : p + q + r + s = 1)
    (hqp : q * p = 0) (hrp : r * p = 0) (hsp : s * p = 0)
    (hpq : p * q = 0) (hpr : p * r = 0) (hps : p * s = 0)
    (hqR : q * R = b • q) (hrR : r * R = c • r)
    (hsR : s * R = d • s)
    (hRq : R * q = b • q) (hRr : R * r = c • r)
    (hRs : R * s = d • s)
    (hid : ∀ k,
      leviCivitaMixedTensorDerivative gInv dg p dp k * p +
          p * leviCivitaMixedTensorDerivative gInv dg p dp k =
        leviCivitaMixedTensorDerivative gInv dg p dp k)
    (hleft : ∀ k,
      leviCivitaMixedTensorDerivative gInv dg R dR k * p +
          R * leviCivitaMixedTensorDerivative gInv dg p dp k =
        da k • p + a • leviCivitaMixedTensorDerivative gInv dg p dp k)
    (hright : ∀ k,
      leviCivitaMixedTensorDerivative gInv dg p dp k * R +
          p * leviCivitaMixedTensorDerivative gInv dg R dR k =
        da k • p + a • leviCivitaMixedTensorDerivative gInv dg p dp k) :
    ∀ k,
      leviCivitaMixedTensorDerivative gInv dg p dp k =
        (a - b)⁻¹ • (q *
          leviCivitaMixedTensorDerivative gInv dg R dR k * p) +
        (a - c)⁻¹ • (r *
          leviCivitaMixedTensorDerivative gInv dg R dR k * p) +
        (a - d)⁻¹ • (s *
          leviCivitaMixedTensorDerivative gInv dg R dR k * p) +
        (a - b)⁻¹ • (p *
          leviCivitaMixedTensorDerivative gInv dg R dR k * q) +
        (a - c)⁻¹ • (p *
          leviCivitaMixedTensorDerivative gInv dg R dR k * r) +
        (a - d)⁻¹ • (p *
          leviCivitaMixedTensorDerivative gInv dg R dR k * s) := by
  intro k
  exact spectralProjectorDerivative_fourBlock
    R (leviCivitaMixedTensorDerivative gInv dg R dR k)
    p (leviCivitaMixedTensorDerivative gInv dg p dp k) q r s
    a b c d (da k) hab hac had hp hsum hqp hrp hsp hpq hpr hps
    hqR hrR hsR hRq hRr hRs (hid k) (hleft k) (hright k)

/-- Coordinate-jet form of the preceding theorem.  Here the hypotheses are
the ordinary differentiated projector/eigen equations.  The connection
derivation lemmas promote them automatically to Levi--Civita identities, so
no covariant-derivative equations need to be supplied separately. -/
theorem leviCivitaSpectralProjectorDerivative_fourBlock_of_coordinateJets
    (gInv : Matrix4) (dg : CoordinateMetricJet1 (Fin 4))
    (R : Matrix4) (dR : Fin 4 → Matrix4)
    (p : Matrix4) (dp : Fin 4 → Matrix4)
    (q r s : Matrix4) (a b c d : ℝ) (da : OneForm4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hp : p * p = p) (hsum : p + q + r + s = 1)
    (hRp : R * p = a • p) (hpR : p * R = a • p)
    (hqp : q * p = 0) (hrp : r * p = 0) (hsp : s * p = 0)
    (hpq : p * q = 0) (hpr : p * r = 0) (hps : p * s = 0)
    (hqR : q * R = b • q) (hrR : r * R = c • r)
    (hsR : s * R = d • s)
    (hRq : R * q = b • q) (hRr : R * r = c • r)
    (hRs : R * s = d • s)
    (hid : ∀ k, dp k * p + p * dp k = dp k)
    (hleft : ∀ k,
      dR k * p + R * dp k = da k • p + a • dp k)
    (hright : ∀ k,
      dp k * R + p * dR k = da k • p + a • dp k) :
    ∀ k,
      leviCivitaMixedTensorDerivative gInv dg p dp k =
        (a - b)⁻¹ • (q *
          leviCivitaMixedTensorDerivative gInv dg R dR k * p) +
        (a - c)⁻¹ • (r *
          leviCivitaMixedTensorDerivative gInv dg R dR k * p) +
        (a - d)⁻¹ • (s *
          leviCivitaMixedTensorDerivative gInv dg R dR k * p) +
        (a - b)⁻¹ • (p *
          leviCivitaMixedTensorDerivative gInv dg R dR k * q) +
        (a - c)⁻¹ • (p *
          leviCivitaMixedTensorDerivative gInv dg R dR k * r) +
        (a - d)⁻¹ • (p *
          leviCivitaMixedTensorDerivative gInv dg R dR k * s) := by
  apply leviCivitaSpectralProjectorDerivative_fourBlock gInv dg R dR
    p dp q r s a b c d da hab hac had hp hsum hqp hrp hsp hpq hpr hps
    hqR hrR hsR hRq hRr hRs
  · intro k
    exact mixedTensorCovariantDerivative_idempotent
      (coordinateChristoffel gInv dg) p dp k hp hid
  · intro k
    exact mixedTensorCovariantDerivative_eigen_left
      (coordinateChristoffel gInv dg) R p dR dp a da k hRp hleft
  · intro k
    exact mixedTensorCovariantDerivative_eigen_right
      (coordinateChristoffel gInv dg) R p dR dp a da k hpR hright

end LeviCivitaProjectorJet

section ScalarBranchForms

/-- Coordinate first jet of a scalar amplitude times an eigen-one-form. -/
def spectralComponentOneFormJet
    (x : ℝ) (dx theta : OneForm4)
    (dtheta : Fin 4 → OneForm4) : Fin 4 → OneForm4 :=
  fun k j => dx k * theta j + x * dtheta k j

/-- Exterior derivative of a coordinate one-form first jet. -/
def oneFormJetExteriorDerivative
    (dtheta : Fin 4 → OneForm4) : Matrix4 :=
  fun k j => dtheta k j - dtheta j k

/-- Explicit product rule for the exterior derivative of a scalar spectral
component: `d(x theta)=dx wedge theta+x dtheta`. -/
theorem spectralComponentOneFormJet_exterior
    (x : ℝ) (dx theta : OneForm4)
    (dtheta : Fin 4 → OneForm4) (k j : Fin 4) :
    oneFormJetExteriorDerivative
        (spectralComponentOneFormJet x dx theta dtheta) k j =
      dx k * theta j - dx j * theta k +
        x * oneFormJetExteriorDerivative dtheta k j := by
  simp only [oneFormJetExteriorDerivative, spectralComponentOneFormJet]
  ring

/-- The reconstructed directional derivatives of the first scalar amplitude,
assembled as a coordinate one-form. -/
noncomputable def reconstructedAmplitudeAOneForm
    (epsilonA x a b qSq : ℝ) (da db dqSq : OneForm4) : OneForm4 :=
  fun k => reconstructedAmplitudeADerivative epsilonA x a b qSq
    (da k) (db k) (dqSq k)

/-- The reconstructed directional derivatives of the second scalar
amplitude, assembled as a coordinate one-form. -/
noncomputable def reconstructedAmplitudeBOneForm
    (epsilonB y a b qSq : ℝ) (da db dqSq : OneForm4) : OneForm4 :=
  fun k => reconstructedAmplitudeBDerivative epsilonB y a b qSq
    (da k) (db k) (dqSq k)

/-- Directionwise differentiated scalar-diagonal identities uniquely force
the complete reconstructed first-amplitude one-form. -/
theorem amplitudeAOneForm_eq_reconstructed
    (epsilonA x a b qSq : ℝ) (dx da db dqSq : OneForm4)
    (hepsilonA : epsilonA ^ 2 = 1) (hx : x ≠ 0)
    (hdiff : ∀ k,
      epsilonA * x * dx k =
        reconstructedDiagonalADerivative a b qSq
          (da k) (db k) (dqSq k)) :
    dx = reconstructedAmplitudeAOneForm epsilonA x a b qSq da db dqSq := by
  have hepsilonA_ne : epsilonA ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at hepsilonA
    norm_num at hepsilonA
  ext k
  apply mul_left_cancel₀ (mul_ne_zero hepsilonA_ne hx)
  exact (hdiff k).trans
    (reconstructedAmplitudeADerivative_relation epsilonA x a b qSq
      (da k) (db k) (dqSq k) hepsilonA hx).symm

/-- Directionwise differentiated scalar-diagonal identities uniquely force
the complete reconstructed second-amplitude one-form. -/
theorem amplitudeBOneForm_eq_reconstructed
    (epsilonB y a b qSq : ℝ) (dy da db dqSq : OneForm4)
    (hepsilonB : epsilonB ^ 2 = 1) (hy : y ≠ 0)
    (hdiff : ∀ k,
      epsilonB * y * dy k =
        reconstructedDiagonalBDerivative a b qSq
          (da k) (db k) (dqSq k)) :
    dy = reconstructedAmplitudeBOneForm epsilonB y a b qSq da db dqSq := by
  have hepsilonB_ne : epsilonB ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at hepsilonB
    norm_num at hepsilonB
  ext k
  apply mul_left_cancel₀ (mul_ne_zero hepsilonB_ne hy)
  exact (hdiff k).trans
    (reconstructedAmplitudeBDerivative_relation epsilonB y a b qSq
      (da k) (db k) (dqSq k) hepsilonB hy).symm

/-- Curvature-reconstructed exterior derivative `dalpha`. -/
noncomputable def curvatureAlphaExteriorDerivative
    (epsilonA x a b qSq : ℝ) (da db dqSq thetaA : OneForm4)
    (dthetaA : Fin 4 → OneForm4) : Matrix4 :=
  oneFormJetExteriorDerivative
    (spectralComponentOneFormJet x
      (reconstructedAmplitudeAOneForm epsilonA x a b qSq da db dqSq)
      thetaA dthetaA)

/-- Curvature-reconstructed exterior derivative `dbeta`. -/
noncomputable def curvatureBetaExteriorDerivative
    (epsilonB y a b qSq : ℝ) (da db dqSq thetaB : OneForm4)
    (dthetaB : Fin 4 → OneForm4) : Matrix4 :=
  oneFormJetExteriorDerivative
    (spectralComponentOneFormJet y
      (reconstructedAmplitudeBOneForm epsilonB y a b qSq da db dqSq)
      thetaB dthetaB)

/-- The displayed formula for `dalpha`, with its amplitude and eigen-one-form
terms separated. -/
theorem curvatureAlphaExteriorDerivative_eq
    (epsilonA x a b qSq : ℝ) (da db dqSq thetaA : OneForm4)
    (dthetaA : Fin 4 → OneForm4) (k j : Fin 4) :
    curvatureAlphaExteriorDerivative epsilonA x a b qSq
        da db dqSq thetaA dthetaA k j =
      reconstructedAmplitudeAOneForm epsilonA x a b qSq da db dqSq k *
          thetaA j -
        reconstructedAmplitudeAOneForm epsilonA x a b qSq da db dqSq j *
          thetaA k +
        x * oneFormJetExteriorDerivative dthetaA k j := by
  exact spectralComponentOneFormJet_exterior x
    (reconstructedAmplitudeAOneForm epsilonA x a b qSq da db dqSq)
    thetaA dthetaA k j

/-- The displayed formula for `dbeta`, with its amplitude and eigen-one-form
terms separated. -/
theorem curvatureBetaExteriorDerivative_eq
    (epsilonB y a b qSq : ℝ) (da db dqSq thetaB : OneForm4)
    (dthetaB : Fin 4 → OneForm4) (k j : Fin 4) :
    curvatureBetaExteriorDerivative epsilonB y a b qSq
        da db dqSq thetaB dthetaB k j =
      reconstructedAmplitudeBOneForm epsilonB y a b qSq da db dqSq k *
          thetaB j -
        reconstructedAmplitudeBOneForm epsilonB y a b qSq da db dqSq j *
          thetaB k +
        y * oneFormJetExteriorDerivative dthetaB k j := by
  exact spectralComponentOneFormJet_exterior y
    (reconstructedAmplitudeBOneForm epsilonB y a b qSq da db dqSq)
    thetaB dthetaB k j

/-- Exteriorization of a one-form jet is skew. -/
theorem oneFormJetExteriorDerivative_transpose
    (dtheta : Fin 4 → OneForm4) :
    (oneFormJetExteriorDerivative dtheta)ᵀ =
      -oneFormJetExteriorDerivative dtheta := by
  ext k j
  simp only [Matrix.transpose_apply, Matrix.neg_apply,
    oneFormJetExteriorDerivative]
  ring

/-- Complete local data needed to evaluate the two scalar spectral branch
forms and their first exterior obstructions.  The roots and their one-form
jets are curvature data; `thetaA,thetaB` and their jets come from the smooth
curvature projectors above; `x,y` are the two nonzero signed amplitude
choices. -/
structure CurvatureScalarBranchJet4 where
  epsilonA : ℝ
  epsilonB : ℝ
  x : ℝ
  y : ℝ
  a : ℝ
  b : ℝ
  qSq : ℝ
  da : OneForm4
  db : OneForm4
  dqSq : OneForm4
  thetaA : OneForm4
  thetaB : OneForm4
  dthetaA : Fin 4 → OneForm4
  dthetaB : Fin 4 → OneForm4

namespace CurvatureScalarBranchJet4

/-- First spectral component `alpha=x thetaA`. -/
def alpha (J : CurvatureScalarBranchJet4) : OneForm4 :=
  J.x • J.thetaA

/-- Second spectral component `beta=y thetaB`. -/
def beta (J : CurvatureScalarBranchJet4) : OneForm4 :=
  J.y • J.thetaB

/-- Curvature-forced coordinate derivative of `alpha`. -/
noncomputable def alphaJet (J : CurvatureScalarBranchJet4) :
    Fin 4 → OneForm4 :=
  spectralComponentOneFormJet J.x
    (reconstructedAmplitudeAOneForm J.epsilonA J.x J.a J.b J.qSq
      J.da J.db J.dqSq) J.thetaA J.dthetaA

/-- Curvature-forced coordinate derivative of `beta`. -/
noncomputable def betaJet (J : CurvatureScalarBranchJet4) :
    Fin 4 → OneForm4 :=
  spectralComponentOneFormJet J.y
    (reconstructedAmplitudeBOneForm J.epsilonB J.y J.a J.b J.qSq
      J.da J.db J.dqSq) J.thetaB J.dthetaB

/-- Exterior obstruction `dalpha`. -/
noncomputable def dalpha (J : CurvatureScalarBranchJet4) : Matrix4 :=
  oneFormJetExteriorDerivative J.alphaJet

/-- Exterior obstruction `dbeta`. -/
noncomputable def dbeta (J : CurvatureScalarBranchJet4) : Matrix4 :=
  oneFormJetExteriorDerivative J.betaJet

/-- Relative-sign sum candidate `vPlus=alpha+beta`. -/
def vPlus (J : CurvatureScalarBranchJet4) : OneForm4 :=
  J.alpha + J.beta

/-- Relative-sign difference candidate `vMinus=alpha-beta`. -/
def vMinus (J : CurvatureScalarBranchJet4) : OneForm4 :=
  J.alpha - J.beta

/-- First jet of the sum candidate. -/
noncomputable def vPlusJet (J : CurvatureScalarBranchJet4) :
    Fin 4 → OneForm4 :=
  J.alphaJet + J.betaJet

/-- First jet of the difference candidate. -/
noncomputable def vMinusJet (J : CurvatureScalarBranchJet4) :
    Fin 4 → OneForm4 :=
  J.alphaJet - J.betaJet

/-- The sum branch has exterior obstruction `dalpha+dbeta`. -/
theorem vPlus_exterior (J : CurvatureScalarBranchJet4) :
    oneFormJetExteriorDerivative J.vPlusJet = J.dalpha + J.dbeta := by
  ext k j
  simp [vPlusJet, dalpha, dbeta, oneFormJetExteriorDerivative]
  ring

/-- The difference branch has exterior obstruction `dalpha-dbeta`. -/
theorem vMinus_exterior (J : CurvatureScalarBranchJet4) :
    oneFormJetExteriorDerivative J.vMinusJet = J.dalpha - J.dbeta := by
  ext k j
  simp [vMinusJet, dalpha, dbeta, oneFormJetExteriorDerivative]
  ring

/-- **II-G2 scalar-branch handoff.** Both curvature candidates close exactly
on the separately integrable locus `dalpha=dbeta=0`.  Away from this locus,
II-G3 only needs to test the two displayed obstruction matrices. -/
theorem both_branches_closed_iff (J : CurvatureScalarBranchJet4) :
    (oneFormJetExteriorDerivative J.vPlusJet = 0 ∧
        oneFormJetExteriorDerivative J.vMinusJet = 0) ↔
      (J.dalpha = 0 ∧ J.dbeta = 0) := by
  rw [J.vPlus_exterior, J.vMinus_exterior]
  exact both_relativeSign_branches_closed_iff LinearMap.id J.dalpha J.dbeta

end CurvatureScalarBranchJet4

/-- Exterior differentiation commutes with the relative-sign sum branch. -/
theorem oneFormJetExteriorDerivative_add
    (dalpha dbeta : Fin 4 → OneForm4) :
    oneFormJetExteriorDerivative (dalpha + dbeta) =
      oneFormJetExteriorDerivative dalpha +
        oneFormJetExteriorDerivative dbeta := by
  ext k j
  simp [oneFormJetExteriorDerivative]
  ring

/-- Exterior differentiation commutes with the relative-sign difference
branch. -/
theorem oneFormJetExteriorDerivative_sub
    (dalpha dbeta : Fin 4 → OneForm4) :
    oneFormJetExteriorDerivative (dalpha - dbeta) =
      oneFormJetExteriorDerivative dalpha -
        oneFormJetExteriorDerivative dbeta := by
  ext k j
  simp [oneFormJetExteriorDerivative]
  ring

/-- **Concrete relative-sign exterior classifier.** For the assembled
curvature branch jets, both relative-sign candidates are closed exactly on
the locus `dalpha=dbeta=0`. -/
theorem both_relativeSign_oneFormJets_closed_iff
    (dalpha dbeta : Fin 4 → OneForm4) :
    (oneFormJetExteriorDerivative (dalpha + dbeta) = 0 ∧
        oneFormJetExteriorDerivative (dalpha - dbeta) = 0) ↔
      (oneFormJetExteriorDerivative dalpha = 0 ∧
        oneFormJetExteriorDerivative dbeta = 0) := by
  rw [oneFormJetExteriorDerivative_add, oneFormJetExteriorDerivative_sub]
  exact both_relativeSign_branches_closed_iff LinearMap.id
    (oneFormJetExteriorDerivative dalpha)
    (oneFormJetExteriorDerivative dbeta)

/-- Coordinate covariant derivative of a covector. -/
noncomputable def covectorCovariantDerivative
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (theta : OneForm4) (dtheta : Fin 4 → OneForm4)
    (k j : Fin 4) : ℝ :=
  dtheta k j - ∑ l, Gamma l k j * theta l

/-- For a torsion-free connection, antisymmetrizing the covariant derivative
of a covector equals the raw coordinate exterior derivative. -/
theorem covectorCovariantDerivative_antisymmetrize
    (Gamma : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (theta : OneForm4) (dtheta : Fin 4 → OneForm4)
    (hGamma : ∀ l k j, Gamma l k j = Gamma l j k)
    (k j : Fin 4) :
    covectorCovariantDerivative Gamma theta dtheta k j -
        covectorCovariantDerivative Gamma theta dtheta j k =
      oneFormJetExteriorDerivative dtheta k j := by
  unfold covectorCovariantDerivative oneFormJetExteriorDerivative
  have hsum : (∑ l, Gamma l k j * theta l) =
      ∑ l, Gamma l j k * theta l := by
    apply Finset.sum_congr rfl
    intro l _
    rw [hGamma l k j]
  rw [hsum]
  ring

/-- The Christoffel symbols constructed from a symmetric metric first jet
therefore give the same antisymmetrized derivative as the coordinate exterior
formula used above. -/
theorem leviCivitaCovectorDerivative_antisymmetrize
    (gInv : Matrix4) (dg : CoordinateMetricJet1 (Fin 4))
    (hdg : ∀ r i j, dg r i j = dg r j i)
    (theta : OneForm4) (dtheta : Fin 4 → OneForm4)
    (k j : Fin 4) :
    covectorCovariantDerivative (coordinateChristoffel gInv dg)
          theta dtheta k j -
        covectorCovariantDerivative (coordinateChristoffel gInv dg)
          theta dtheta j k =
      oneFormJetExteriorDerivative dtheta k j := by
  apply covectorCovariantDerivative_antisymmetrize
  intro l k' j'
  exact coordinateChristoffel_symm gInv dg hdg l k' j'

end ScalarBranchForms

end RainichKaluza
