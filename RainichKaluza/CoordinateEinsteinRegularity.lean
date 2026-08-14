import RainichKaluza.CoordinateEinstein
import RainichKaluza.CoordinateRicciRegularity

/-!
# Regularity closure for the literal coordinate Einstein field

This file packages componentwise `C³` metric regularity into the genuine
three-jet differentiability and Schwarz symmetries needed by
`CoordinateEinstein`.  At a Minkowski normal-coordinate point this removes
all of the metric-jet and composed-Ricci regularity side conditions from
contracted Bianchi.
-/

namespace RainichKaluza

open scoped Matrix Topology ContDiff

set_option maxHeartbeats 2000000

/-- Scalar-curvature first-jet factorization with no redundant Ricci
regularity hypothesis. -/
theorem scalarFieldCoordinateFDeriv_actualCoordinateScalarCurvatureField4'
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (r : Fin 4) :
    scalarFieldCoordinateFDeriv
        (actualCoordinateScalarCurvatureField4 g) z r =
      coordinateScalarCurvatureFirstJet
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (actualCoordinateMetricJet2Field4 g z)
        (actualCoordinateMetricJet3Field4 g z) r :=
  scalarFieldCoordinateFDeriv_actualCoordinateScalarCurvatureField4
    g z hreg hdet
      (differentiableAt_actualCoordinateRicciCovariantField4 g z hreg hdet) r

/-- Einstein first-jet factorization with no redundant Ricci regularity
hypothesis. -/
theorem scalarFieldCoordinateFDeriv_actualCoordinateEinsteinField4'
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ actualCoordinateEinsteinField4 g y i j) z r =
      coordinateEinsteinCovariantFirstJet
        (coordinateMetricMatrixField4 g z)
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (actualCoordinateMetricJet2Field4 g z)
        (actualCoordinateMetricJet3Field4 g z) r i j :=
  scalarFieldCoordinateFDeriv_actualCoordinateEinsteinField4
    g z hreg hdet
      (differentiableAt_actualCoordinateRicciCovariantField4 g z hreg hdet)
      r i j

/-- The actual Einstein divergence factors through the finite metric
three-jet without any separately assumed Ricci regularity. -/
theorem actualCoordinateEinsteinContractedDivergenceAt4_eq_coordinate'
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (j : Fin 4) :
    actualCoordinateEinsteinContractedDivergenceAt4 g z j =
      coordinateCovariant2Divergence
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (fun i k ↦ coordinateEinsteinCovariant
          (coordinateMetricMatrixField4 g z)
          ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
          (actualCoordinateMetricJet1Field4 g z)
          (actualCoordinateMetricJet2Field4 g z) i k)
        (fun r i k ↦ coordinateEinsteinCovariantFirstJet
          (coordinateMetricMatrixField4 g z)
          ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
          (actualCoordinateMetricJet1Field4 g z)
          (actualCoordinateMetricJet2Field4 g z)
          (actualCoordinateMetricJet3Field4 g z) r i k) j :=
  actualCoordinateEinsteinContractedDivergenceAt4_eq_coordinate
    g z hreg hdet
      (differentiableAt_actualCoordinateRicciCovariantField4 g z hreg hdet) j

/-! ## A natural `C³` source for the genuine three-jet hypotheses -/

/-- Componentwise `C³` regularity of the coordinate metric matrix at one
point. -/
def CoordinateMetricComponentsContDiffThreeAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  ∀ i j, ContDiffAt ℝ 3
    (fun y ↦ coordinateMetricMatrixField4 g y i j) z

private theorem scalarFieldCoordinateFDeriv_nested_eq
    (f : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r s : Fin 4)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) z) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ scalarFieldCoordinateFDeriv f y s) z r =
      fderiv ℝ (fderiv ℝ f) z
        (curvatureCoordinateDirection r)
        (curvatureCoordinateDirection s) := by
  unfold scalarFieldCoordinateFDeriv
  rw [fderiv_clm_apply hf (by fun_prop)]
  simp

/-- Componentwise `C³` metric regularity supplies the exact pointwise
regularity package used by the Ricci and Einstein first-jet chain rules. -/
theorem CoordinateMetricComponentsContDiffThreeAt4.threeJetDifferentiableAt
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : CoordinateMetricComponentsContDiffThreeAt4 g z) :
    CoordinateMetricThreeJetDifferentiableAt4 g z := by
  constructor
  · intro i j
    exact (h i j).differentiableAt (by norm_num)
  · intro r i j
    unfold actualCoordinateMetricJet1Field4
      scalarFieldCoordinateFDeriv
    have hDf : ContDiffAt ℝ 2
        (fderiv ℝ (fun y ↦ coordinateMetricMatrixField4 g y i j)) z :=
      (h i j).fderiv_right (m := 2) (by norm_num)
    exact (hDf.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  · intro r s i j
    unfold actualCoordinateMetricJet2Field4
      actualCoordinateMetricJet1Field4 scalarFieldCoordinateFDeriv
    let f : CurvatureCoordinateSpace4 → ℝ :=
      fun y ↦ coordinateMetricMatrixField4 g y i j
    have hDf : ContDiffAt ℝ 2 (fderiv ℝ f) z :=
      (h i j).fderiv_right (m := 2) (by norm_num)
    have hDfs : ContDiffAt ℝ 2
        (fun y ↦ fderiv ℝ f y (curvatureCoordinateDirection s)) z :=
      hDf.clm_apply contDiffAt_const
    have hDDfs : ContDiffAt ℝ 1
        (fderiv ℝ
          (fun y ↦ fderiv ℝ f y (curvatureCoordinateDirection s))) z :=
      hDfs.fderiv_right (m := 1) (by norm_num)
    exact (hDDfs.clm_apply contDiffAt_const).differentiableAt (by norm_num)

/-- The first two derivative slots of the genuine metric third jet commute
under componentwise `C³` regularity. -/
theorem actualCoordinateMetricJet3Field4_swap12_of_contDiffThreeAt
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : CoordinateMetricComponentsContDiffThreeAt4 g z)
    (a b c i j : Fin 4) :
    actualCoordinateMetricJet3Field4 g z a b c i j =
      actualCoordinateMetricJet3Field4 g z b a c i j := by
  let f : CurvatureCoordinateSpace4 → ℝ :=
    fun y ↦ coordinateMetricMatrixField4 g y i j
  let fc : CurvatureCoordinateSpace4 → ℝ :=
    fun y ↦ scalarFieldCoordinateFDeriv f y c
  have hDf : ContDiffAt ℝ 2 (fderiv ℝ f) z :=
    (h i j).fderiv_right (m := 2) (by norm_num)
  have hfc : ContDiffAt ℝ 2 fc z := by
    dsimp [fc]
    unfold scalarFieldCoordinateFDeriv
    exact hDf.clm_apply contDiffAt_const
  have hDfc : DifferentiableAt ℝ (fderiv ℝ fc) z :=
    (hfc.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hsymm := hfc.isSymmSndFDerivAt (by norm_num)
  unfold actualCoordinateMetricJet3Field4
  change scalarFieldCoordinateFDeriv
      (fun y ↦ scalarFieldCoordinateFDeriv fc y b) z a =
    scalarFieldCoordinateFDeriv
      (fun y ↦ scalarFieldCoordinateFDeriv fc y a) z b
  rw [scalarFieldCoordinateFDeriv_nested_eq fc z a b hDfc,
    scalarFieldCoordinateFDeriv_nested_eq fc z b a hDfc]
  exact hsymm _ _

/-- The second and third derivative slots of the genuine metric third jet
also commute under componentwise `C³` regularity.  The proof uses Schwarz at
all points in a neighborhood and then differentiates the resulting local
Hessian equality. -/
theorem actualCoordinateMetricJet3Field4_swap23_of_contDiffThreeAt
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : CoordinateMetricComponentsContDiffThreeAt4 g z)
    (a b c i j : Fin 4) :
    actualCoordinateMetricJet3Field4 g z a b c i j =
      actualCoordinateMetricJet3Field4 g z a c b i j := by
  let f : CurvatureCoordinateSpace4 → ℝ :=
    fun y ↦ coordinateMetricMatrixField4 g y i j
  have hC3 : ∀ᶠ y in nhds z, ContDiffAt ℝ 3 f y := by
    exact (h i j).eventually (by norm_num)
  have hessian :
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f x c) y b) =ᶠ[nhds z]
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f x b) y c) := by
    filter_upwards [hC3] with y hy
    have hDf : DifferentiableAt ℝ (fderiv ℝ f) y :=
      (hy.fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
    have hsymm := hy.isSymmSndFDerivAt (by norm_num)
    calc
      scalarFieldCoordinateFDeriv
          (fun x ↦ scalarFieldCoordinateFDeriv f x c) y b =
        fderiv ℝ (fderiv ℝ f) y
          (curvatureCoordinateDirection b)
          (curvatureCoordinateDirection c) :=
        scalarFieldCoordinateFDeriv_nested_eq f y b c hDf
      _ = fderiv ℝ (fderiv ℝ f) y
          (curvatureCoordinateDirection c)
          (curvatureCoordinateDirection b) := hsymm _ _
      _ = scalarFieldCoordinateFDeriv
          (fun x ↦ scalarFieldCoordinateFDeriv f x b) y c :=
        (scalarFieldCoordinateFDeriv_nested_eq f y c b hDf).symm
  unfold actualCoordinateMetricJet3Field4
  change scalarFieldCoordinateFDeriv
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f x c) y b) z a =
    scalarFieldCoordinateFDeriv
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f x b) y c) z a
  unfold scalarFieldCoordinateFDeriv
  exact DFunLike.congr_fun hessian.fderiv_eq
    (curvatureCoordinateDirection a)

/-- The metric field is symmetric on some neighborhood of the point. -/
def CoordinateMetricSymmetricNear4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  ∀ᶠ y in nhds z, (continuousBilinFormToBilin (g y)).IsSymm

/-- Neighborhood symmetry of the metric field propagates through all three
nested coordinate derivatives, so the two metric-component slots of the
actual third jet commute. -/
theorem actualCoordinateMetricJet3Field4_metric_swap_of_symmetricNear
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : CoordinateMetricSymmetricNear4 g z)
    (a b c i j : Fin 4) :
    actualCoordinateMetricJet3Field4 g z a b c i j =
      actualCoordinateMetricJet3Field4 g z a b c j i := by
  let f : CurvatureCoordinateSpace4 → ℝ :=
    fun y ↦ coordinateMetricMatrixField4 g y i j
  let f' : CurvatureCoordinateSpace4 → ℝ :=
    fun y ↦ coordinateMetricMatrixField4 g y j i
  have h0 : f =ᶠ[nhds z] f' := by
    filter_upwards [h] with y hy
    dsimp [f, f', coordinateMetricMatrixField4]
    exact hy.eq _ _
  have h1clm : fderiv ℝ f =ᶠ[nhds z] fderiv ℝ f' := h0.fderiv
  have h1 :
      (fun y ↦ scalarFieldCoordinateFDeriv f y c) =ᶠ[nhds z]
      (fun y ↦ scalarFieldCoordinateFDeriv f' y c) := by
    filter_upwards [h1clm] with y hy
    exact DFunLike.congr_fun hy (curvatureCoordinateDirection c)
  have h2clm : fderiv ℝ
      (fun y ↦ scalarFieldCoordinateFDeriv f y c) =ᶠ[nhds z]
      fderiv ℝ
      (fun y ↦ scalarFieldCoordinateFDeriv f' y c) := h1.fderiv
  have h2 :
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f x c) y b) =ᶠ[nhds z]
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f' x c) y b) := by
    filter_upwards [h2clm] with y hy
    exact DFunLike.congr_fun hy (curvatureCoordinateDirection b)
  unfold actualCoordinateMetricJet3Field4
  change scalarFieldCoordinateFDeriv
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f x c) y b) z a =
    scalarFieldCoordinateFDeriv
      (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ scalarFieldCoordinateFDeriv f' x c) y b) z a
  unfold scalarFieldCoordinateFDeriv
  exact DFunLike.congr_fun h2.fderiv_eq
    (curvatureCoordinateDirection a)

/-- Contracted Bianchi for an actual `C³`, symmetric metric field at a
Minkowski normal-coordinate point.  Every formal metric-jet regularity and
symmetry hypothesis is discharged, including differentiability of the
composed coordinate Ricci field. -/
theorem actualCoordinateEinsteinField4_contractedBianchi_of_minkowskiNormal_C3
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hC3 : CoordinateMetricComponentsContDiffThreeAt4 g z)
    (hsymm : CoordinateMetricSymmetricNear4 g z)
    (hmetric : coordinateMetricMatrixField4 g z = minkowskiMetric)
    (hfirst : actualCoordinateMetricJet1Field4 g z = 0)
    (j : Fin 4) :
    actualCoordinateEinsteinContractedDivergenceAt4 g z j = 0 := by
  have hreg := hC3.threeJetDifferentiableAt
  have hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0 := by
    rw [hmetric, minkowskiMetric_det]
    norm_num
  have hRic :=
    differentiableAt_actualCoordinateRicciCovariantField4 g z hreg hdet
  exact actualCoordinateEinsteinField4_contractedBianchi_of_minkowskiNormal
    g z hreg hRic
      hmetric hfirst
      (actualCoordinateMetricJet3Field4_swap12_of_contDiffThreeAt hC3)
      (actualCoordinateMetricJet3Field4_swap23_of_contDiffThreeAt hC3)
      (actualCoordinateMetricJet3Field4_metric_swap_of_symmetricNear hsymm)
      j

end RainichKaluza
