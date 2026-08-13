import RainichKaluza.FourthOrderMetricDetector

/-!
# Coordinate-germ locality of the actual-metric detector

This file proves extensionality under equality of two coordinate metric
fields on a neighborhood of the evaluation point.  It does not assert
covariance under a change of coordinates or identify the construction with
an abstract four-jet invariant.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Filter

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

private theorem fderivField_eventuallyEq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : E → F} {z : E} (h : Filter.EventuallyEq (nhds z) f f') :
    Filter.EventuallyEq (nhds z)
      (fun y ↦ fderiv ℝ f y) (fun y ↦ fderiv ℝ f' y) := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  exact Filter.EventuallyEq.fderiv_eq hy

theorem coordinateMetricMatrixField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (coordinateMetricMatrixField4 g)
      (coordinateMetricMatrixField4 g') := by
  filter_upwards [h] with y hy
  funext i j
  exact congrArg
    (fun B : ContinuousBilinForm CurvatureCoordinateSpace4 ↦
      B (curvatureCoordinateDirection i) (curvatureCoordinateDirection j)) hy

theorem actualCoordinateMetricJet1Field4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualCoordinateMetricJet1Field4 g)
      (actualCoordinateMetricJet1Field4 g') := by
  have hG := coordinateMetricMatrixField4_eventuallyEq h
  filter_upwards [hG.eventuallyEq_nhds] with y hy
  funext r i j
  unfold actualCoordinateMetricJet1Field4 scalarFieldCoordinateFDeriv
  have hc :
      (fun x : CurvatureCoordinateSpace4 ↦
        coordinateMetricMatrixField4 g x i j) =ᶠ[nhds y]
      (fun x : CurvatureCoordinateSpace4 ↦
        coordinateMetricMatrixField4 g' x i j) := by
    filter_upwards [hy] with x hx
    exact congrFun (congrFun hx i) j
  rw [Filter.EventuallyEq.fderiv_eq hc]

theorem actualCoordinateMetricJet2Field4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualCoordinateMetricJet2Field4 g)
      (actualCoordinateMetricJet2Field4 g') := by
  have hJ1 := actualCoordinateMetricJet1Field4_eventuallyEq h
  filter_upwards [hJ1.eventuallyEq_nhds] with y hy
  funext r s i j
  unfold actualCoordinateMetricJet2Field4 scalarFieldCoordinateFDeriv
  have hc :
      (fun x : CurvatureCoordinateSpace4 ↦
        actualCoordinateMetricJet1Field4 g x s i j) =ᶠ[nhds y]
      (fun x : CurvatureCoordinateSpace4 ↦
        actualCoordinateMetricJet1Field4 g' x s i j) := by
    filter_upwards [hy] with x hx
    exact congrFun (congrFun (congrFun hx s) i) j
  rw [Filter.EventuallyEq.fderiv_eq hc]

theorem actualCoordinateRicciCovariantField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualCoordinateRicciCovariantField4 g)
      (actualCoordinateRicciCovariantField4 g') := by
  have hG := coordinateMetricMatrixField4_eventuallyEq h
  have hJ1 := actualCoordinateMetricJet1Field4_eventuallyEq h
  have hJ2 := actualCoordinateMetricJet2Field4_eventuallyEq h
  filter_upwards [hG, hJ1, hJ2] with y hGy hJ1y hJ2y
  funext i j
  unfold actualCoordinateRicciCovariantField4
  rw [hGy, hJ1y, hJ2y]

theorem actualMixedRicciField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualMixedRicciField4 g)
      (actualMixedRicciField4 g') := by
  have hG := coordinateMetricMatrixField4_eventuallyEq h
  have hRic := actualCoordinateRicciCovariantField4_eventuallyEq h
  filter_upwards [hG, hRic] with y hGy hRicy
  unfold actualMixedRicciField4
  rw [hGy, hRicy]

theorem actualRicciCharacteristicDataField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualRicciCharacteristicDataField4 g)
      (actualRicciCharacteristicDataField4 g') := by
  filter_upwards [actualMixedRicciField4_eventuallyEq h] with y hy
  unfold actualRicciCharacteristicDataField4
  rw [hy]

theorem actualRicciReconstructedQSqField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualRicciReconstructedQSqField4 g)
      (actualRicciReconstructedQSqField4 g') := by
  filter_upwards [actualMixedRicciField4_eventuallyEq h] with y hy
  unfold actualRicciReconstructedQSqField4
  rw [hy]

theorem actualRicciComplementaryDiscriminantField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualRicciComplementaryDiscriminantField4 g)
      (actualRicciComplementaryDiscriminantField4 g') := by
  filter_upwards [actualRicciCharacteristicDataField4_eventuallyEq h] with y hy
  unfold actualRicciComplementaryDiscriminantField4
  rw [hy]

theorem actualRicciComplementaryRootAField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootAField4 g') := by
  have hd := actualRicciCharacteristicDataField4_eventuallyEq h
  have hdisc := actualRicciComplementaryDiscriminantField4_eventuallyEq h
  filter_upwards [hd, hdisc] with y hdy hdiscy
  unfold actualRicciComplementaryRootAField4
  rw [hdy, hdiscy]

theorem actualRicciComplementaryRootBField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualRicciComplementaryRootBField4 g)
      (actualRicciComplementaryRootBField4 g') := by
  have hd := actualRicciCharacteristicDataField4_eventuallyEq h
  have hdisc := actualRicciComplementaryDiscriminantField4_eventuallyEq h
  filter_upwards [hd, hdisc] with y hdy hdiscy
  unfold actualRicciComplementaryRootBField4
  rw [hdy, hdiscy]

theorem actualRicciProtectedRootField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z) (actualRicciProtectedRootField4 g)
      (actualRicciProtectedRootField4 g') := by
  filter_upwards [actualRicciReconstructedQSqField4_eventuallyEq h] with y hy
  unfold actualRicciProtectedRootField4
  rw [hy]

theorem actualRicciComplementaryProjectorAField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualRicciComplementaryProjectorAField4 g)
      (actualRicciComplementaryProjectorAField4 g') := by
  have hR := actualMixedRicciField4_eventuallyEq h
  have ha := actualRicciComplementaryRootAField4_eventuallyEq h
  have hb := actualRicciComplementaryRootBField4_eventuallyEq h
  have hq := actualRicciProtectedRootField4_eventuallyEq h
  filter_upwards [hR, ha, hb, hq] with y hRy hay hby hqy
  unfold actualRicciComplementaryProjectorAField4
    matrixFourRootProjectorField matrixEigenFactorField
  rw [hRy, hay, hby, hqy]
  simp only [hqy]

theorem actualRicciComplementaryProjectorBField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualRicciComplementaryProjectorBField4 g)
      (actualRicciComplementaryProjectorBField4 g') := by
  have hR := actualMixedRicciField4_eventuallyEq h
  have ha := actualRicciComplementaryRootAField4_eventuallyEq h
  have hb := actualRicciComplementaryRootBField4_eventuallyEq h
  have hq := actualRicciProtectedRootField4_eventuallyEq h
  filter_upwards [hR, ha, hb, hq] with y hRy hay hby hqy
  unfold actualRicciComplementaryProjectorBField4
    matrixFourRootProjectorField matrixEigenFactorField
  rw [hRy, hay, hby, hqy]
  simp only [hqy]

theorem scalarFieldCoordinateFDeriv_eq_of_eventuallyEq
    {f f' : CurvatureCoordinateSpace4 → ℝ}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) f f') :
    scalarFieldCoordinateFDeriv f z = scalarFieldCoordinateFDeriv f' z := by
  funext k
  unfold scalarFieldCoordinateFDeriv
  rw [Filter.EventuallyEq.fderiv_eq h]

private theorem smoothMatrixProjectedVectorFDeriv_eq_of_eventuallyEq
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe u z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) P P') :
    smoothMatrixProjectedVectorFDeriv P probe z u =
      smoothMatrixProjectedVectorFDeriv P' probe z u := by
  funext i
  unfold smoothMatrixProjectedVectorFDeriv
  apply Finset.sum_congr rfl
  intro j _
  have hij :
      Filter.EventuallyEq (nhds z) (fun x => P x i j) (fun x => P' x i j) := by
    filter_upwards [h] with x hx
    exact congrFun (congrFun hx i) j
  rw [Filter.EventuallyEq.fderiv_eq hij]

private theorem smoothProjectedMetricPairingFDeriv_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe u z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    smoothProjectedMetricPairingFDeriv g P probe z u =
      smoothProjectedMetricPairingFDeriv g' P' probe z u := by
  have hg0 := hg.self_of_nhds
  have hP0 := hP.self_of_nhds
  have hdP := smoothMatrixProjectedVectorFDeriv_eq_of_eventuallyEq
    (probe := probe) (u := u) hP
  unfold smoothProjectedMetricPairingFDeriv smoothMatrixProjectedVector
  rw [Filter.EventuallyEq.fderiv_eq hg, hg0, hP0, hdP]

private theorem smoothNormalizeTimelikeProjectedFDeriv_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe u z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    smoothNormalizeTimelikeProjectedFDeriv g P probe z u =
      smoothNormalizeTimelikeProjectedFDeriv g' P' probe z u := by
  have hg0 := hg.self_of_nhds
  have hP0 := hP.self_of_nhds
  have hdP := smoothMatrixProjectedVectorFDeriv_eq_of_eventuallyEq
    (probe := probe) (u := u) hP
  have hpair := smoothProjectedMetricPairingFDeriv_eq_of_eventuallyEq
    (probe := probe) (u := u) hg hP
  unfold smoothNormalizeTimelikeProjectedFDeriv timelikeNormalizationScale
    smoothMetricPairing smoothMatrixProjectedVector
  dsimp only
  rw [hg0, hP0, hdP, hpair]

private theorem smoothNormalizeSpacelikeProjectedFDeriv_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe u z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    smoothNormalizeSpacelikeProjectedFDeriv g P probe z u =
      smoothNormalizeSpacelikeProjectedFDeriv g' P' probe z u := by
  have hg0 := hg.self_of_nhds
  have hP0 := hP.self_of_nhds
  have hdP := smoothMatrixProjectedVectorFDeriv_eq_of_eventuallyEq
    (probe := probe) (u := u) hP
  have hpair := smoothProjectedMetricPairingFDeriv_eq_of_eventuallyEq
    (probe := probe) (u := u) hg hP
  unfold smoothNormalizeSpacelikeProjectedFDeriv spacelikeNormalizationScale
    smoothMetricPairing smoothMatrixProjectedVector
  dsimp only
  rw [hg0, hP0, hdP, hpair]

private theorem smoothNormalizeTimelike_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    smoothNormalizeTimelike g (smoothMatrixProjectedVector P probe) z =
      smoothNormalizeTimelike g' (smoothMatrixProjectedVector P' probe) z := by
  unfold smoothNormalizeTimelike smoothMetricPairing smoothMatrixProjectedVector
  rw [hg.self_of_nhds, hP.self_of_nhds]

private theorem smoothNormalizeSpacelike_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    smoothNormalizeSpacelike g (smoothMatrixProjectedVector P probe) z =
      smoothNormalizeSpacelike g' (smoothMatrixProjectedVector P' probe) z := by
  unfold smoothNormalizeSpacelike smoothMetricPairing smoothMatrixProjectedVector
  rw [hg.self_of_nhds, hP.self_of_nhds]

private theorem smoothTimelikeCurvatureEigenCovector_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    smoothTimelikeCurvatureEigenCovector g P probe z =
      smoothTimelikeCurvatureEigenCovector g' P' probe z := by
  have hg0 := hg.self_of_nhds
  have hP0 := hP.self_of_nhds
  have hn := smoothNormalizeTimelike_eq_of_eventuallyEq
    (probe := probe) hg hP
  unfold smoothTimelikeCurvatureEigenCovector smoothMetricDualCovector
  rw [hg0, hn]

private theorem smoothSpacelikeCurvatureEigenCovector_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    smoothSpacelikeCurvatureEigenCovector g P probe z =
      smoothSpacelikeCurvatureEigenCovector g' P' probe z := by
  have hg0 := hg.self_of_nhds
  have hP0 := hP.self_of_nhds
  have hn := smoothNormalizeSpacelike_eq_of_eventuallyEq
    (probe := probe) hg hP
  unfold smoothSpacelikeCurvatureEigenCovector smoothMetricDualCovector
  rw [hg0, hn]

private theorem timelikeCurvatureEigenCovectorCoordinateJet_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    timelikeCurvatureEigenCovectorCoordinateJet g P probe z =
      timelikeCurvatureEigenCovectorCoordinateJet g' P' probe z := by
  have hg0 := hg.self_of_nhds
  have hnorm := smoothNormalizeTimelike_eq_of_eventuallyEq
    (probe := probe) hg hP
  have hdnorm (u : CurvatureCoordinateSpace4) :=
    smoothNormalizeTimelikeProjectedFDeriv_eq_of_eventuallyEq
      (probe := probe) (u := u) hg hP
  funext k j
  unfold timelikeCurvatureEigenCovectorCoordinateJet
    smoothTimelikeCurvatureEigenCovectorFDeriv
  rw [Filter.EventuallyEq.fderiv_eq hg, hg0,
    hnorm, hdnorm (curvatureCoordinateDirection k)]

private theorem spacelikeCurvatureEigenCovectorCoordinateJet_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    {probe z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hP : Filter.EventuallyEq (nhds z) P P') :
    spacelikeCurvatureEigenCovectorCoordinateJet g P probe z =
      spacelikeCurvatureEigenCovectorCoordinateJet g' P' probe z := by
  have hg0 := hg.self_of_nhds
  have hnorm := smoothNormalizeSpacelike_eq_of_eventuallyEq
    (probe := probe) hg hP
  have hdnorm (u : CurvatureCoordinateSpace4) :=
    smoothNormalizeSpacelikeProjectedFDeriv_eq_of_eventuallyEq
      (probe := probe) (u := u) hg hP
  funext k j
  unfold spacelikeCurvatureEigenCovectorCoordinateJet
    smoothSpacelikeCurvatureEigenCovectorFDeriv
  rw [Filter.EventuallyEq.fderiv_eq hg, hg0,
    hnorm, hdnorm (curvatureCoordinateDirection k)]

private theorem concreteFixedProbeCurvatureScalarBranchJet4_eq_of_eventuallyEq
    {a a' b b' qSq qSq' : CurvatureCoordinateSpace4 → ℝ}
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {PA PA' PB PB' : CurvatureCoordinateSpace4 → Matrix4}
    {epsilonA epsilonB : ℝ}
    {probeA probeB z : CurvatureCoordinateSpace4}
    (ha : Filter.EventuallyEq (nhds z) a a')
    (hb : Filter.EventuallyEq (nhds z) b b')
    (hq : Filter.EventuallyEq (nhds z) qSq qSq')
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hPA : Filter.EventuallyEq (nhds z) PA PA')
    (hPB : Filter.EventuallyEq (nhds z) PB PB') :
    concreteFixedProbeCurvatureScalarBranchJet4 epsilonA epsilonB
        a b qSq g PA PB probeA probeB z =
      concreteFixedProbeCurvatureScalarBranchJet4 epsilonA epsilonB
        a' b' qSq' g' PA' PB' probeA probeB z := by
  have hthetaA := congrArg continuousCovectorCoordinates
    (smoothTimelikeCurvatureEigenCovector_eq_of_eventuallyEq
      (probe := probeA) hg hPA)
  have hthetaB := congrArg continuousCovectorCoordinates
    (smoothSpacelikeCurvatureEigenCovector_eq_of_eventuallyEq
      (probe := probeB) hg hPB)
  have hdthetaA :=
    timelikeCurvatureEigenCovectorCoordinateJet_eq_of_eventuallyEq
      (probe := probeA) hg hPA
  have hdthetaB :=
    spacelikeCurvatureEigenCovectorCoordinateJet_eq_of_eventuallyEq
      (probe := probeB) hg hPB
  have hx : reconstructedScalarAmplitudeA epsilonA a b qSq z =
      reconstructedScalarAmplitudeA epsilonA a' b' qSq' z := by
    unfold reconstructedScalarAmplitudeA smoothScalarAmplitude
      reconstructedDiagonalAField
    rw [ha.self_of_nhds, hb.self_of_nhds, hq.self_of_nhds]
  have hy : reconstructedScalarAmplitudeB epsilonB a b qSq z =
      reconstructedScalarAmplitudeB epsilonB a' b' qSq' z := by
    unfold reconstructedScalarAmplitudeB smoothScalarAmplitude
      reconstructedDiagonalBField
    rw [ha.self_of_nhds, hb.self_of_nhds, hq.self_of_nhds]
  unfold concreteFixedProbeCurvatureScalarBranchJet4
  rw [hx, hy, ha.self_of_nhds, hb.self_of_nhds, hq.self_of_nhds,
    scalarFieldCoordinateFDeriv_eq_of_eventuallyEq ha,
    scalarFieldCoordinateFDeriv_eq_of_eventuallyEq hb,
    scalarFieldCoordinateFDeriv_eq_of_eventuallyEq hq,
    hthetaA, hthetaB, hdthetaA, hdthetaB]

theorem actualMetricScalarBranchJetField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (timelikeProbe spacelikeProbe : Fin 4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricScalarBranchJetField4 g timelikeProbe spacelikeProbe)
      (actualMetricScalarBranchJetField4 g' timelikeProbe spacelikeProbe) := by
  have ha := actualRicciComplementaryRootAField4_eventuallyEq h
  have hb := actualRicciComplementaryRootBField4_eventuallyEq h
  have hq := actualRicciReconstructedQSqField4_eventuallyEq h
  have hPA := actualRicciComplementaryProjectorAField4_eventuallyEq h
  have hPB := actualRicciComplementaryProjectorBField4_eventuallyEq h
  filter_upwards [ha.eventuallyEq_nhds, hb.eventuallyEq_nhds,
    hq.eventuallyEq_nhds, h.eventuallyEq_nhds,
    hPA.eventuallyEq_nhds, hPB.eventuallyEq_nhds] with
      y hay hby hqy hgy hPAy hPBy
  unfold actualMetricScalarBranchJetField4
  exact concreteFixedProbeCurvatureScalarBranchJet4_eq_of_eventuallyEq
    hay hby hqy hgy hPAy hPBy

theorem actualMetricScalarOneFormCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (timelikeProbe spacelikeProbe : Fin 4) (relativeMinus : Bool)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricScalarOneFormCandidateField4 g
        timelikeProbe spacelikeProbe relativeMinus)
      (actualMetricScalarOneFormCandidateField4 g'
        timelikeProbe spacelikeProbe relativeMinus) := by
  filter_upwards [actualMetricScalarBranchJetField4_eventuallyEq
    timelikeProbe spacelikeProbe h] with y hy
  unfold actualMetricScalarOneFormCandidateField4
  rw [hy]

theorem actualMetricScalarClosureObstruction4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (timelikeProbe spacelikeProbe : Fin 4) (relativeMinus : Bool)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricScalarClosureObstruction4 g
        timelikeProbe spacelikeProbe relativeMinus)
      (actualMetricScalarClosureObstruction4 g'
        timelikeProbe spacelikeProbe relativeMinus) := by
  filter_upwards [actualMetricScalarBranchJetField4_eventuallyEq
    timelikeProbe spacelikeProbe h] with y hy
  unfold actualMetricScalarClosureObstruction4
  rw [hy]

theorem actualMetricScalarContributionCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricScalarContributionCandidateField4 g choice)
      (actualMetricScalarContributionCandidateField4 g' choice) := by
  have hG := coordinateMetricMatrixField4_eventuallyEq h
  have hv := actualMetricScalarOneFormCandidateField4_eventuallyEq
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus h
  filter_upwards [hG, hv] with y hGy hvy
  unfold actualMetricScalarContributionCandidateField4
    scalarContributionMatrixField scalarRaisedVector
  funext i j
  dsimp only
  rw [hGy, hvy]

theorem actualMetricMaxwellResidualCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellResidualCandidateField4 g choice)
      (actualMetricMaxwellResidualCandidateField4 g' choice) := by
  have hR := actualMixedRicciField4_eventuallyEq h
  have hV := actualMetricScalarContributionCandidateField4_eventuallyEq choice h
  filter_upwards [hR, hV] with y hRy hVy
  unfold actualMetricMaxwellResidualCandidateField4
    curvatureMaxwellResidualField
  rw [hRy, hVy]

theorem actualMetricMaxwellMinusProjectorCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellMinusProjectorCandidateField4 g choice)
      (actualMetricMaxwellMinusProjectorCandidateField4 g' choice) := by
  have hS := actualMetricMaxwellResidualCandidateField4_eventuallyEq choice h
  have hq := actualRicciReconstructedQSqField4_eventuallyEq h
  filter_upwards [hS, hq] with y hSy hqy
  unfold actualMetricMaxwellMinusProjectorCandidateField4
    curvatureMaxwellMinusProjectorField matrixMaxwellMinusProjectorField
    positiveMaxwellMagnitudeFromSquare
  rw [hSy, hqy]

theorem actualMetricMaxwellPlusProjectorCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellPlusProjectorCandidateField4 g choice)
      (actualMetricMaxwellPlusProjectorCandidateField4 g' choice) := by
  have hS := actualMetricMaxwellResidualCandidateField4_eventuallyEq choice h
  have hq := actualRicciReconstructedQSqField4_eventuallyEq h
  filter_upwards [hS, hq] with y hSy hqy
  unfold actualMetricMaxwellPlusProjectorCandidateField4
    curvatureMaxwellPlusProjectorField matrixMaxwellPlusProjectorField
    positiveMaxwellMagnitudeFromSquare
  rw [hSy, hqy]

private theorem smoothMatrixProjectedVector_eventuallyEq
    {P P' : CurvatureCoordinateSpace4 → Matrix4}
    (probe : CurvatureCoordinateSpace4) {z : CurvatureCoordinateSpace4}
    (hP : Filter.EventuallyEq (nhds z) P P') :
    Filter.EventuallyEq (nhds z)
      (smoothMatrixProjectedVector P probe)
      (smoothMatrixProjectedVector P' probe) := by
  filter_upwards [hP] with y hy
  unfold smoothMatrixProjectedVector
  rw [hy]

theorem actualMetricMaxwellMinusProbe0Field4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellMinusProbe0Field4 g choice)
      (actualMetricMaxwellMinusProbe0Field4 g' choice) := by
  exact smoothMatrixProjectedVector_eventuallyEq _
    (actualMetricMaxwellMinusProjectorCandidateField4_eventuallyEq choice h)

theorem actualMetricMaxwellMinusProbe1Field4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellMinusProbe1Field4 g choice)
      (actualMetricMaxwellMinusProbe1Field4 g' choice) := by
  exact smoothMatrixProjectedVector_eventuallyEq _
    (actualMetricMaxwellMinusProjectorCandidateField4_eventuallyEq choice h)

theorem actualMetricMaxwellPlusProbe0Field4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g' choice) := by
  exact smoothMatrixProjectedVector_eventuallyEq _
    (actualMetricMaxwellPlusProjectorCandidateField4_eventuallyEq choice h)

theorem actualMetricMaxwellPlusProbe1Field4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellPlusProbe1Field4 g choice)
      (actualMetricMaxwellPlusProbe1Field4 g' choice) := by
  exact smoothMatrixProjectedVector_eventuallyEq _
    (actualMetricMaxwellPlusProjectorCandidateField4_eventuallyEq choice h)

theorem actualMetricMaxwellLorentzPivotCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g' choice) := by
  have hx := actualMetricMaxwellMinusProbe0Field4_eventuallyEq choice h
  have hy := actualMetricMaxwellMinusProbe1Field4_eventuallyEq choice h
  filter_upwards [h, hx, hy] with w hgw hxw hyw
  unfold actualMetricMaxwellLorentzPivotCandidateField4
    smoothLorentzianPivotCandidate
  split <;> simp only [hgw, hxw, hyw, smoothMetricPairing]

theorem actualMetricMaxwellLorentzCompanionCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)
      (actualMetricMaxwellLorentzCompanionCandidateField4 g' choice) := by
  have hx := actualMetricMaxwellMinusProbe0Field4_eventuallyEq choice h
  have hy := actualMetricMaxwellMinusProbe1Field4_eventuallyEq choice h
  filter_upwards [hx, hy] with w hxw hyw
  unfold actualMetricMaxwellLorentzCompanionCandidateField4
    smoothLorentzianPivotCompanion
  split <;> simp only [hxw, hyw]

theorem actualMetricPrincipalTetradCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricPrincipalTetradCandidateField4 g choice)
      (actualMetricPrincipalTetradCandidateField4 g' choice) := by
  have hu0 := actualMetricMaxwellLorentzPivotCandidateField4_eventuallyEq choice h
  have hu1 := actualMetricMaxwellLorentzCompanionCandidateField4_eventuallyEq choice h
  have hv0 := actualMetricMaxwellPlusProbe0Field4_eventuallyEq choice h
  have hv1 := actualMetricMaxwellPlusProbe1Field4_eventuallyEq choice h
  have huOrth : Filter.EventuallyEq (nhds z)
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g'
        (actualMetricMaxwellLorentzPivotCandidateField4 g' choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g' choice)) := by
    filter_upwards [h, hu0, hu1] with w hgw hu0w hu1w
    unfold smoothMetricOrthogonalizeSecond smoothMetricPairing
    rw [hgw, hu0w, hu1w]
  have hvOrth : Filter.EventuallyEq (nhds z)
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g'
        (actualMetricMaxwellPlusProbe0Field4 g' choice)
        (actualMetricMaxwellPlusProbe1Field4 g' choice)) := by
    filter_upwards [h, hv0, hv1] with w hgw hv0w hv1w
    unfold smoothMetricOrthogonalizeSecond smoothMetricPairing
    rw [hgw, hv0w, hv1w]
  filter_upwards [h, hu0, huOrth, hv0, hvOrth] with
      w hgw hu0w huOrthw hv0w hvOrthw
  unfold actualMetricPrincipalTetradCandidateField4
    smoothPrincipalTetradFromFields smoothLorentzianPlaneFrame
    smoothSpacelikePlaneFrame smoothNormalizeTimelike
    smoothNormalizeSpacelike smoothMetricPairing
  rw [hgw, hu0w, huOrthw, hv0w, hvOrthw]

theorem actualMetricPrincipalFrameCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricPrincipalFrameCandidateField4 g choice)
      (actualMetricPrincipalFrameCandidateField4 g' choice) := by
  filter_upwards [actualMetricPrincipalTetradCandidateField4_eventuallyEq
    choice h] with w hw
  unfold actualMetricPrincipalFrameCandidateField4
    smoothPrincipalFrameMatrix smoothPrincipalTetradVector
  rw [hw]

theorem actualMetricPrincipalCoframeCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricPrincipalCoframeCandidateField4 g choice)
      (actualMetricPrincipalCoframeCandidateField4 g' choice) := by
  filter_upwards [actualMetricPrincipalFrameCandidateField4_eventuallyEq
    choice h] with w hw
  unfold actualMetricPrincipalCoframeCandidateField4
  rw [hw]

private theorem scalarContributionTraceField_eventuallyEq
    {G G' : CurvatureCoordinateSpace4 → Matrix4}
    {v v' : CurvatureCoordinateSpace4 → OneForm4}
    {z : CurvatureCoordinateSpace4}
    (hG : Filter.EventuallyEq (nhds z) G G')
    (hv : Filter.EventuallyEq (nhds z) v v') :
    Filter.EventuallyEq (nhds z)
      (scalarContributionTraceField G v)
      (scalarContributionTraceField G' v') := by
  filter_upwards [hG, hv] with w hGw hvw
  unfold scalarContributionTraceField scalarRaisedVector
  rw [hGw, hvw]

theorem actualMetricReconstructionObstruction4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricReconstructionObstruction4 g choice)
      (actualMetricReconstructionObstruction4 g' choice) := by
  have hR := actualMixedRicciField4_eventuallyEq h
  have hV := actualMetricScalarContributionCandidateField4_eventuallyEq choice h
  have hq := actualRicciReconstructedQSqField4_eventuallyEq h
  have hG := coordinateMetricMatrixField4_eventuallyEq h
  have hv := actualMetricScalarOneFormCandidateField4_eventuallyEq
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus h
  have htrace := scalarContributionTraceField_eventuallyEq
    (G := fun y => (coordinateMetricMatrixField4 g y)⁻¹)
    (G' := fun y => (coordinateMetricMatrixField4 g' y)⁻¹)
    (v := actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe choice.relativeMinus)
    (v' := actualMetricScalarOneFormCandidateField4 g'
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe choice.relativeMinus)
    (hG.fun_comp (fun G => G⁻¹)) hv
  filter_upwards [hR, hV, htrace, hq] with w hRw hVw htw hqw
  unfold actualMetricReconstructionObstruction4
  rw [hRw, hVw, htw, hqw]

theorem actualMetricElectricSeedCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricElectricSeedCandidateField4 g choice)
      (actualMetricElectricSeedCandidateField4 g' choice) := by
  have hL := actualMetricPrincipalCoframeCandidateField4_eventuallyEq choice h
  have hq := actualRicciReconstructedQSqField4_eventuallyEq h
  filter_upwards [hL, hq] with w hLw hqw
  unfold actualMetricElectricSeedCandidateField4
    positiveMaxwellMagnitudeFromSquare
  rw [hLw, hqw]

theorem actualMetricHodgeElectricSeedCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricHodgeElectricSeedCandidateField4 g choice)
      (actualMetricHodgeElectricSeedCandidateField4 g' choice) := by
  have hG := coordinateMetricMatrixField4_eventuallyEq h
  have hE := actualMetricElectricSeedCandidateField4_eventuallyEq choice h
  filter_upwards [hG, hE] with w hGw hEw
  unfold actualMetricHodgeElectricSeedCandidateField4
  rw [hGw, hEw]

theorem actualMetricTransportedHodgeSeedCandidateField4_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    Filter.EventuallyEq (nhds z)
      (actualMetricTransportedHodgeSeedCandidateField4 g choice)
      (actualMetricTransportedHodgeSeedCandidateField4 g' choice) := by
  have hL := actualMetricPrincipalCoframeCandidateField4_eventuallyEq choice h
  have hq := actualRicciReconstructedQSqField4_eventuallyEq h
  filter_upwards [hL, hq] with w hLw hqw
  unfold actualMetricTransportedHodgeSeedCandidateField4
    positiveMaxwellMagnitudeFromSquare
  rw [hLw, hqw]

private theorem matrixFieldCoordinateFDeriv4_eq_of_eventuallyEq
    {L L' : CurvatureCoordinateSpace4 → Matrix4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) L L') :
    matrixFieldCoordinateFDeriv4 L z = matrixFieldCoordinateFDeriv4 L' z := by
  funext k i j
  unfold matrixFieldCoordinateFDeriv4 scalarFieldCoordinateFDeriv
  have hij : Filter.EventuallyEq (nhds z)
      (fun y => L y i j) (fun y => L' y i j) := by
    filter_upwards [h] with y hy
    exact congrFun (congrFun hy i) j
  rw [Filter.EventuallyEq.fderiv_eq hij]

theorem curvatureSeedCanonicalChannelField_eventuallyEq
    {L L' : CurvatureCoordinateSpace4 → Matrix4}
    {q q' : CurvatureCoordinateSpace4 → ℝ}
    {z : CurvatureCoordinateSpace4}
    (hL : Filter.EventuallyEq (nhds z) L L')
    (hq : Filter.EventuallyEq (nhds z) q q') :
    Filter.EventuallyEq (nhds z)
      (curvatureSeedCanonicalChannelField L q)
      (curvatureSeedCanonicalChannelField L' q') := by
  filter_upwards [hL.eventuallyEq_nhds, hq.eventuallyEq_nhds] with
      w hLw hqw
  have hdL := matrixFieldCoordinateFDeriv4_eq_of_eventuallyEq hLw
  have hdq := scalarFieldCoordinateFDeriv_eq_of_eventuallyEq hqw
  unfold curvatureSeedCanonicalChannelField
  rw [hLw.self_of_nhds, hqw.self_of_nhds, hdL, hdq]

theorem curvatureSeedCosineField_eventuallyEq_of_inputGerms
    {L L' : CurvatureCoordinateSpace4 → Matrix4}
    {q q' : CurvatureCoordinateSpace4 → ℝ}
    {v v' : CurvatureCoordinateSpace4 → OneForm4}
    {source : Fin 4} {z : CurvatureCoordinateSpace4}
    (hL : Filter.EventuallyEq (nhds z) L L')
    (hq : Filter.EventuallyEq (nhds z) q q')
    (hv : Filter.EventuallyEq (nhds z) v v') :
    Filter.EventuallyEq (nhds z)
      (curvatureSeedCosineField L q v source)
      (curvatureSeedCosineField L' q' v' source) := by
  have hX := curvatureSeedCanonicalChannelField_eventuallyEq hL hq
  filter_upwards [hL, hq, hv, hX] with w hLw hqw hvw hXw
  unfold curvatureSeedCosineField
  rw [hLw, hqw, hvw, hXw]

theorem curvatureSeedCosineCoordinateDerivative_eq_of_inputGerms
    {L L' : CurvatureCoordinateSpace4 → Matrix4}
    {q q' : CurvatureCoordinateSpace4 → ℝ}
    {v v' : CurvatureCoordinateSpace4 → OneForm4}
    {source : Fin 4} {z : CurvatureCoordinateSpace4}
    (hL : Filter.EventuallyEq (nhds z) L L')
    (hq : Filter.EventuallyEq (nhds z) q q')
    (hv : Filter.EventuallyEq (nhds z) v v') :
    curvatureSeedCosineCoordinateDerivative L q v source z =
      curvatureSeedCosineCoordinateDerivative L' q' v' source z := by
  unfold curvatureSeedCosineCoordinateDerivative
  exact scalarFieldCoordinateFDeriv_eq_of_eventuallyEq
    (curvatureSeedCosineField_eventuallyEq_of_inputGerms hL hq hv)

theorem IsCurvatureSeedFourthOrderCandidateAt_iff_of_inputGerms
    {L L' : CurvatureCoordinateSpace4 → Matrix4}
    {q q' : CurvatureCoordinateSpace4 → ℝ}
    {v v' : CurvatureCoordinateSpace4 → OneForm4}
    {z : CurvatureCoordinateSpace4}
    (choice : FourthOrderComponentChoice)
    (hL : Filter.EventuallyEq (nhds z) L L')
    (hq : Filter.EventuallyEq (nhds z) q q')
    (hv : Filter.EventuallyEq (nhds z) v v') :
    IsCurvatureSeedFourthOrderCandidateAt L q v z choice ↔
      IsCurvatureSeedFourthOrderCandidateAt L' q' v' z choice := by
  have hdL := matrixFieldCoordinateFDeriv4_eq_of_eventuallyEq hL
  have hdq := scalarFieldCoordinateFDeriv_eq_of_eventuallyEq hq
  have hdA := curvatureSeedCosineCoordinateDerivative_eq_of_inputGerms
    (source := choice.1) hL hq hv
  unfold IsCurvatureSeedFourthOrderCandidateAt
  rw [hL.self_of_nhds, hq.self_of_nhds, hv.self_of_nhds, hdL, hdq, hdA]

theorem curvatureSeedFourthOrderCouplingSqCandidateAt_eq_of_inputGerms
    {L L' : CurvatureCoordinateSpace4 → Matrix4}
    {q q' : CurvatureCoordinateSpace4 → ℝ}
    {v v' : CurvatureCoordinateSpace4 → OneForm4}
    {z : CurvatureCoordinateSpace4}
    (choice : FourthOrderComponentChoice)
    (hL : Filter.EventuallyEq (nhds z) L L')
    (hq : Filter.EventuallyEq (nhds z) q q')
    (hv : Filter.EventuallyEq (nhds z) v v') :
    curvatureSeedFourthOrderCouplingSqCandidateAt L q v z choice =
      curvatureSeedFourthOrderCouplingSqCandidateAt L' q' v' z choice := by
  have hdL := matrixFieldCoordinateFDeriv4_eq_of_eventuallyEq hL
  have hdq := scalarFieldCoordinateFDeriv_eq_of_eventuallyEq hq
  have hdA := curvatureSeedCosineCoordinateDerivative_eq_of_inputGerms
    (source := choice.1) hL hq hv
  unfold curvatureSeedFourthOrderCouplingSqCandidateAt
  rw [hL.self_of_nhds, hq.self_of_nhds, hv.self_of_nhds, hdL, hdq, hdA]

theorem positiveMaxwellMagnitudeFromSquare_eventuallyEq
    {qSq qSq' : CurvatureCoordinateSpace4 → ℝ}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) qSq qSq') :
    Filter.EventuallyEq (nhds z)
      (positiveMaxwellMagnitudeFromSquare qSq)
      (positiveMaxwellMagnitudeFromSquare qSq') := by
  filter_upwards [h] with w hw
  unfold positiveMaxwellMagnitudeFromSquare
  rw [hw]

/-- The numerical detector output depends only on the coordinate metric germ
at the evaluation point. -/
theorem actualMetricFourthOrderCouplingSqCandidateAt_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      actualMetricFourthOrderCouplingSqCandidateAt g' z choice := by
  apply curvatureSeedFourthOrderCouplingSqCandidateAt_eq_of_inputGerms
  · exact actualMetricPrincipalCoframeCandidateField4_eventuallyEq choice h
  · exact positiveMaxwellMagnitudeFromSquare_eventuallyEq
      (actualRicciReconstructedQSqField4_eventuallyEq h)
  · exact actualMetricScalarOneFormCandidateField4_eventuallyEq
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus h

private theorem reconstructedDiagonalAField_eventuallyEq
    {a a' b b' qSq qSq' : CurvatureCoordinateSpace4 → ℝ}
    {z : CurvatureCoordinateSpace4}
    (ha : Filter.EventuallyEq (nhds z) a a')
    (hb : Filter.EventuallyEq (nhds z) b b')
    (hq : Filter.EventuallyEq (nhds z) qSq qSq') :
    Filter.EventuallyEq (nhds z)
      (reconstructedDiagonalAField a b qSq)
      (reconstructedDiagonalAField a' b' qSq') := by
  filter_upwards [ha, hb, hq] with w haw hbw hqw
  unfold reconstructedDiagonalAField
  rw [haw, hbw, hqw]

private theorem reconstructedDiagonalBField_eventuallyEq
    {a a' b b' qSq qSq' : CurvatureCoordinateSpace4 → ℝ}
    {z : CurvatureCoordinateSpace4}
    (ha : Filter.EventuallyEq (nhds z) a a')
    (hb : Filter.EventuallyEq (nhds z) b b')
    (hq : Filter.EventuallyEq (nhds z) qSq qSq') :
    Filter.EventuallyEq (nhds z)
      (reconstructedDiagonalBField a b qSq)
      (reconstructedDiagonalBField a' b' qSq') := by
  filter_upwards [ha, hb, hq] with w haw hbw hqw
  unfold reconstructedDiagonalBField
  rw [haw, hbw, hqw]

private theorem smoothMetricPairing_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {x x' y y' : CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hx : Filter.EventuallyEq (nhds z) x x')
    (hy : Filter.EventuallyEq (nhds z) y y') :
    Filter.EventuallyEq (nhds z)
      (smoothMetricPairing g x y) (smoothMetricPairing g' x' y') := by
  filter_upwards [hg, hx, hy] with w hgw hxw hyw
  unfold smoothMetricPairing
  rw [hgw, hxw, hyw]

private theorem smoothMetricOrthogonalizeSecond_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {x x' y y' : CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (hg : Filter.EventuallyEq (nhds z) g g')
    (hx : Filter.EventuallyEq (nhds z) x x')
    (hy : Filter.EventuallyEq (nhds z) y y') :
    Filter.EventuallyEq (nhds z)
      (smoothMetricOrthogonalizeSecond g x y)
      (smoothMetricOrthogonalizeSecond g' x' y') := by
  filter_upwards [hg, hx, hy] with w hgw hxw hyw
  unfold smoothMetricOrthogonalizeSecond smoothMetricPairing
  rw [hgw, hxw, hyw]

theorem isActualMetricAlgebraicEntranceAt4_iff_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    IsActualMetricAlgebraicEntranceAt4 g z ↔
      IsActualMetricAlgebraicEntranceAt4 g' z := by
  have hG := (coordinateMetricMatrixField4_eventuallyEq h).self_of_nhds
  have hR := (actualMixedRicciField4_eventuallyEq h).self_of_nhds
  have hd := (actualRicciCharacteristicDataField4_eventuallyEq h).self_of_nhds
  have hqSq := (actualRicciReconstructedQSqField4_eventuallyEq h).self_of_nhds
  have hq := (actualRicciProtectedRootField4_eventuallyEq h).self_of_nhds
  have ha := (actualRicciComplementaryRootAField4_eventuallyEq h).self_of_nhds
  have hb := (actualRicciComplementaryRootBField4_eventuallyEq h).self_of_nhds
  have hPA := (actualRicciComplementaryProjectorAField4_eventuallyEq h).self_of_nhds
  have hPB := (actualRicciComplementaryProjectorBField4_eventuallyEq h).self_of_nhds
  have hdisc :=
    (actualRicciComplementaryDiscriminantField4_eventuallyEq h).self_of_nhds
  unfold IsActualMetricAlgebraicEntranceAt4
  rw [hG, hR, hd, hqSq, hq, ha, hb, hPA, hPB, hdisc]

theorem isActualMetricMaxwellEntranceAt4_iff_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    IsActualMetricMaxwellEntranceAt4 g choice z ↔
      IsActualMetricMaxwellEntranceAt4 g' choice z := by
  have hG := (coordinateMetricMatrixField4_eventuallyEq h).self_of_nhds
  have hq := (actualRicciReconstructedQSqField4_eventuallyEq h).self_of_nhds
  have hS :=
    (actualMetricMaxwellResidualCandidateField4_eventuallyEq choice h).self_of_nhds
  have hP :=
    (actualMetricMaxwellMinusProjectorCandidateField4_eventuallyEq choice h).self_of_nhds
  have hQ :=
    (actualMetricMaxwellPlusProjectorCandidateField4_eventuallyEq choice h).self_of_nhds
  unfold IsActualMetricMaxwellEntranceAt4
  rw [hG, hq, hS, hP, hQ]

theorem isActualMetricHodgeCompatibleAt4_iff_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    IsActualMetricHodgeCompatibleAt4 g choice z ↔
      IsActualMetricHodgeCompatibleAt4 g' choice z := by
  have hE :=
    (actualMetricHodgeElectricSeedCandidateField4_eventuallyEq choice h).self_of_nhds
  have hH :=
    (actualMetricTransportedHodgeSeedCandidateField4_eventuallyEq choice h).self_of_nhds
  unfold IsActualMetricHodgeCompatibleAt4
  rw [hE, hH]

theorem isActualMetricUpstreamEntranceAt4_iff_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    IsActualMetricUpstreamEntranceAt4 g z choice ↔
      IsActualMetricUpstreamEntranceAt4 g' z choice := by
  have ha := actualRicciComplementaryRootAField4_eventuallyEq h
  have hb := actualRicciComplementaryRootBField4_eventuallyEq h
  have hq := actualRicciReconstructedQSqField4_eventuallyEq h
  have hPA := actualRicciComplementaryProjectorAField4_eventuallyEq h
  have hPB := actualRicciComplementaryProjectorBField4_eventuallyEq h
  have hdiagA := (reconstructedDiagonalAField_eventuallyEq ha hb hq).self_of_nhds
  have hdiagB := (reconstructedDiagonalBField_eventuallyEq ha hb hq).self_of_nhds
  have hpA := smoothMatrixProjectedVector_eventuallyEq
    (curvatureCoordinateDirection choice.scalarTimelikeProbe) hPA
  have hpB := smoothMatrixProjectedVector_eventuallyEq
    (curvatureCoordinateDirection choice.scalarSpacelikeProbe) hPB
  have hpairA := (smoothMetricPairing_eventuallyEq h hpA hpA).self_of_nhds
  have hpairB := (smoothMetricPairing_eventuallyEq h hpB hpB).self_of_nhds
  have hclosure := (actualMetricScalarClosureObstruction4_eventuallyEq
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus h).self_of_nhds
  have hreconstruction :=
    (actualMetricReconstructionObstruction4_eventuallyEq choice h).self_of_nhds
  have hu0 := actualMetricMaxwellLorentzPivotCandidateField4_eventuallyEq choice h
  have hu1 :=
    actualMetricMaxwellLorentzCompanionCandidateField4_eventuallyEq choice h
  have hv0 := actualMetricMaxwellPlusProbe0Field4_eventuallyEq choice h
  have hv1 := actualMetricMaxwellPlusProbe1Field4_eventuallyEq choice h
  have huOrth := smoothMetricOrthogonalizeSecond_eventuallyEq h hu0 hu1
  have hvOrth := smoothMetricOrthogonalizeSecond_eventuallyEq h hv0 hv1
  have hpairU0 := (smoothMetricPairing_eventuallyEq h hu0 hu0).self_of_nhds
  have hpairUOrth :=
    (smoothMetricPairing_eventuallyEq h huOrth huOrth).self_of_nhds
  have hpairV0 := (smoothMetricPairing_eventuallyEq h hv0 hv0).self_of_nhds
  have hpairVOrth :=
    (smoothMetricPairing_eventuallyEq h hvOrth hvOrth).self_of_nhds
  have halgebraic := isActualMetricAlgebraicEntranceAt4_iff_of_eventuallyEq h
  have hmaxwell := isActualMetricMaxwellEntranceAt4_iff_of_eventuallyEq choice h
  have hhodge := isActualMetricHodgeCompatibleAt4_iff_of_eventuallyEq choice h
  unfold IsActualMetricUpstreamEntranceAt4
  dsimp only
  rw [halgebraic, hdiagA, hdiagB, hpairA, hpairB, hclosure,
    hreconstruction, hmaxwell, hhodge, hpairU0, hpairUOrth,
    hpairV0, hpairVOrth]

/-- Complete pointwise detector acceptance depends only on the coordinate
metric germ at the evaluation point. -/
theorem isActualMetricFourthOrderDetectorCandidateAt_iff_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (choice : ActualMetricDetectorChoice4)
    (h : Filter.EventuallyEq (nhds z) g g') :
    IsActualMetricFourthOrderDetectorCandidateAt g z choice ↔
      IsActualMetricFourthOrderDetectorCandidateAt g' z choice := by
  have hL := actualMetricPrincipalCoframeCandidateField4_eventuallyEq choice h
  have hq := positiveMaxwellMagnitudeFromSquare_eventuallyEq
    (actualRicciReconstructedQSqField4_eventuallyEq h)
  have hv := actualMetricScalarOneFormCandidateField4_eventuallyEq
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus h
  have hupstream := isActualMetricUpstreamEntranceAt4_iff_of_eventuallyEq choice h
  have hchannel := IsCurvatureSeedFourthOrderCandidateAt_iff_of_inputGerms
    choice.channel hL hq hv
  unfold IsActualMetricFourthOrderDetectorCandidateAt
  dsimp only
  rw [hupstream, hchannel]

/-- The complete finite accepted-choice set is extensional in the coordinate
metric germ. -/
theorem acceptedActualMetricFourthOrderDetectorChoicesAt_eq_of_eventuallyEq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    acceptedActualMetricFourthOrderDetectorChoicesAt g z =
      acceptedActualMetricFourthOrderDetectorChoicesAt g' z := by
  classical
  ext choice
  rw [mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff,
    mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff]
  exact isActualMetricFourthOrderDetectorCandidateAt_iff_of_eventuallyEq
    choice h

/-- **Complete coordinate-germ extensionality.** Neighborhood-equal
coordinate metric fields have the same finite accepted detector set and the
same numerical output for every raw finite choice.  This is a locality
theorem in a fixed coordinate trivialization, not a coordinate-covariance
statement. -/
theorem actualMetricFourthOrderDetector_coordinateGerm_extensionality
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : Filter.EventuallyEq (nhds z) g g') :
    acceptedActualMetricFourthOrderDetectorChoicesAt g z =
        acceptedActualMetricFourthOrderDetectorChoicesAt g' z ∧
      ∀ choice : ActualMetricDetectorChoice4,
        actualMetricFourthOrderCouplingSqCandidateAt g z choice =
          actualMetricFourthOrderCouplingSqCandidateAt g' z choice := by
  exact ⟨acceptedActualMetricFourthOrderDetectorChoicesAt_eq_of_eventuallyEq h,
    fun choice =>
      actualMetricFourthOrderCouplingSqCandidateAt_eq_of_eventuallyEq choice h⟩

set_option linter.constructorNameAsVariable true

end RainichKaluza
