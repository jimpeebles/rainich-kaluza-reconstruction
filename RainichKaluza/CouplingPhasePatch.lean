import RainichKaluza.CouplingPhasePropagation
import RainichKaluza.PhaseIIITransportedSeedCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Patchwise propagation of the coupling circle

The pointwise detector equations give the complementary phase laws

`dA = -2 B omega`, `dB = 2 A omega`.

This file upgrades their algebraic cancellation to a neighborhood theorem.
On an open convex patch on which the reconstructed scalar components really
have those Frechet derivatives, `A^2 + B^2` is constant.  Consequently the
single base-point normalization `A^2 + B^2 = 3` propagates across the whole
patch.

The differentiability hypotheses are deliberately explicit: a pointwise
detector output is not, by itself, a differentiable choice of fields on a
neighborhood.
-/

namespace RainichKaluza

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two phase laws give the genuine zero Frechet derivative of the
coupling-square function. -/
theorem hasFDerivAt_couplingSq_eq_zero_of_phaseLaws
    (A B : E → ℝ) (omega : E →L[ℝ] ℝ) (x : E)
    (hA : HasFDerivAt A ((-2 * B x) • omega) x)
    (hB : HasFDerivAt B ((2 * A x) • omega) x) :
    HasFDerivAt (A * A + B * B) (0 : E →L[ℝ] ℝ) x := by
  have h := (hA.mul hA).add (hB.mul hB)
  have hzero :
      A x • ((-2 * B x) • omega) + A x • ((-2 * B x) • omega) +
          (B x • ((2 * A x) • omega) + B x • ((2 * A x) • omega)) =
        (0 : E →L[ℝ] ℝ) := by
    ext u
    simp
    ring
  exact h.congr_fderiv hzero

/-- If the complementary phase laws hold as actual Frechet derivative
identities throughout an open convex patch, then `A^2 + B^2` has the same
value at every two points of that patch. -/
theorem couplingSq_eq_of_phaseLaws_on_openConvex
    (U : Set E) (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (A B : E → ℝ) (omega : E → E →L[ℝ] ℝ)
    (hA : ∀ x ∈ U, HasFDerivAt A ((-2 * B x) • omega x) x)
    (hB : ∀ x ∈ U, HasFDerivAt B ((2 * A x) • omega x) x)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    A x ^ 2 + B x ^ 2 = A y ^ 2 + B y ^ 2 := by
  let K : E → ℝ := A * A + B * B
  have hK : ∀ z ∈ U, HasFDerivAt K (0 : E →L[ℝ] ℝ) z := by
    intro z hz
    exact hasFDerivAt_couplingSq_eq_zero_of_phaseLaws
      A B (omega z) z (hA z hz) (hB z hz)
  have hconst := hUopen.is_const_of_fderiv_eq_zero hUconvex.isPreconnected
    (fun z hz => (hK z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hK z hz).fderiv) hx hy
  simpa only [K, Pi.add_apply, Pi.mul_apply, pow_two] using hconst

/-- A single normalized point fixes the Kaluza coupling circle on the whole
open convex patch. -/
theorem couplingSq_eq_three_of_phaseLaws_on_openConvex
    (U : Set E) (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (A B : E → ℝ) (omega : E → E →L[ℝ] ℝ)
    (hA : ∀ x ∈ U, HasFDerivAt A ((-2 * B x) • omega x) x)
    (hB : ∀ x ∈ U, HasFDerivAt B ((2 * A x) • omega x) x)
    {x0 : E} (hx0 : x0 ∈ U) (hbase : A x0 ^ 2 + B x0 ^ 2 = 3) :
    ∀ x ∈ U, A x ^ 2 + B x ^ 2 = 3 := by
  intro x hx
  calc
    A x ^ 2 + B x ^ 2 = A x0 ^ 2 + B x0 ^ 2 :=
      couplingSq_eq_of_phaseLaws_on_openConvex U hUopen hUconvex A B omega
        hA hB hx hx0
    _ = 3 := hbase

/-- **Patchwise detector bridge.**  For differentiable reconstructed fields,
the existing cosine-component detector equation together with the proposed
sine-component propagation equation imply the normalized coupling circle on
the whole patch from one base point.

This theorem makes the regularity and fixed-patch hypotheses explicit; it
does not identify `A`, `B`, `eta`, or `Jv` with a particular raw branch
choice. -/
theorem couplingSq_eq_three_of_detectorPhaseEquations_on_openConvex
    (U : Set CurvatureCoordinateSpace4)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (A B : CurvatureCoordinateSpace4 → ℝ)
    (eta Jv : CurvatureCoordinateSpace4 → OneForm4)
    (hAdiff : ∀ x ∈ U, DifferentiableAt ℝ A x)
    (hBdiff : ∀ x ∈ U, DifferentiableAt ℝ B x)
    (hAeq : ∀ x ∈ U,
      nextOrderSineCouplingEquation
        (scalarFieldCoordinateFDeriv A x) (eta x) (Jv x) (B x) = 0)
    (hBeq : ∀ x ∈ U,
      sineCouplingPropagationEquation
        (scalarFieldCoordinateFDeriv B x) (eta x) (Jv x) (A x) (B x) = 0)
    {x0 : CurvatureCoordinateSpace4} (hx0 : x0 ∈ U)
    (hbase : A x0 ^ 2 + B x0 ^ 2 = 3) :
    ∀ x ∈ U, A x ^ 2 + B x ^ 2 = 3 := by
  apply couplingSq_eq_three_of_phaseLaws_on_openConvex U hUopen hUconvex
    A B
    (fun x => oneForm4ContinuousLinearMap
      (phaseOneFormFromEffectiveChannel (eta x) (Jv x) (B x)))
  · intro x hx
    have hdA : scalarFieldCoordinateFDeriv A x =
        (-2 * B x) • phaseOneFormFromEffectiveChannel (eta x) (Jv x) (B x) := by
      apply sub_eq_zero.mp
      rw [← nextOrderSineCouplingEquation_eq_phaseLawResidual]
      exact hAeq x hx
    have h := hasFDerivAt_of_coordinateFDeriv A _ x (hAdiff x hx) hdA
    simpa only [oneForm4ContinuousLinearMap_smul] using h
  · intro x hx
    have hdB : scalarFieldCoordinateFDeriv B x =
        (2 * A x) • phaseOneFormFromEffectiveChannel (eta x) (Jv x) (B x) :=
      (sineCouplingPropagationEquation_eq_zero_iff
        (scalarFieldCoordinateFDeriv B x) (eta x) (Jv x) (A x) (B x)).mp
        (hBeq x hx)
    have h := hasFDerivAt_of_coordinateFDeriv B _ x (hBdiff x hx) hdB
    simpa only [oneForm4ContinuousLinearMap_smul] using h
  · exact hx0
  · exact hbase

/-- One *fixed* raw fourth-order channel choice accepted throughout a patch.
The acceptance predicate includes the non-null seed gate, reproduction of
both complete seed channels, the chosen nonzero wedge denominator, and the
four-component cosine propagation equation.

This is intentionally weaker than a full actual-metric entrance package: it
isolates the persistent raw-channel datum needed by the phase argument.  Its
stored covectors all live in one common trivialization.  The literal metric
detector instead uses a moving principal frame; the frame-correct adapter is
`actualMetricFixedFourthOrderChannelPatch`, and its propagation theorem is
in `ActualMetricCouplingPhasePatch`. -/
structure FixedFourthOrderChannelPatch
    (U : Set CurvatureCoordinateSpace4) where
  seedAmplitude : CurvatureCoordinateSpace4 → ℝ
  scalarCovector : CurvatureCoordinateSpace4 → OneForm4
  cosineDerivative : CurvatureCoordinateSpace4 → OneForm4
  channels : CurvatureCoordinateSpace4 → ThreeTensor4 × ThreeTensor4
  choice : FourthOrderComponentChoice
  accepted : ∀ x ∈ U,
    IsFourthOrderChannelCandidate
      (seedAmplitude x) (scalarCovector x) (cosineDerivative x)
      (channels x) choice

namespace FixedFourthOrderChannelPatch

variable {U : Set CurvatureCoordinateSpace4}

/-- Reconstructed effective one-form for the fixed raw choice. -/
noncomputable def effectiveOneForm
    (P : FixedFourthOrderChannelPatch U) :
    CurvatureCoordinateSpace4 → OneForm4 :=
  fun x => canonicalEffectiveOneFormFromChannels
    (P.seedAmplitude x) (P.channels x)

/-- Reconstructed cosine double-angle component for the fixed raw choice. -/
noncomputable def cosineComponent
    (P : FixedFourthOrderChannelPatch U) :
    CurvatureCoordinateSpace4 → ℝ :=
  fun x => canonicalCosineCandidateFromChannels
    (P.seedAmplitude x) (P.scalarCovector x) (P.channels x) P.choice.1

/-- Reconstructed sine double-angle component for the fixed raw choice. -/
noncomputable def sineComponent
    (P : FixedFourthOrderChannelPatch U) :
    CurvatureCoordinateSpace4 → ℝ :=
  fun x => fourthOrderSineCandidate
    (P.seedAmplitude x) (P.scalarCovector x) (P.cosineDerivative x)
    (P.channels x) P.choice

/-- Principal-reflected scalar covector used in the channel shear. -/
def reflectedScalarCovector
    (P : FixedFourthOrderChannelPatch U) :
    CurvatureCoordinateSpace4 → OneForm4 :=
  fun x => canonicalPrincipalReflectionCovector (P.scalarCovector x)

/-- Persistent acceptance really retains the complete two-channel identity,
not just the quotient components used to read `A` and `B`. -/
theorem completeChannels
    (P : FixedFourthOrderChannelPatch U) (x : CurvatureCoordinateSpace4)
    (hx : x ∈ U) :
    P.channels x = canonicalComplexionCouplingChannels
      (P.seedAmplitude x) (P.scalarCovector x)
      (P.effectiveOneForm x) (P.cosineComponent x) := by
  exact (P.accepted x hx).2.1.2

/-- The fourth-order cosine-component phase equation carried by persistent
acceptance. -/
theorem cosinePhaseEquation
    (P : FixedFourthOrderChannelPatch U) (x : CurvatureCoordinateSpace4)
    (hx : x ∈ U) :
    nextOrderSineCouplingEquation
      (P.cosineDerivative x) (P.effectiveOneForm x)
      (P.reflectedScalarCovector x) (P.sineComponent x) = 0 := by
  exact (P.accepted x hx).2.2.2

/-- **Fixed-choice patch propagation.**  Persistent acceptance supplies the
entire fourth-order `dA` equation.  Once its stored covector is certified as
the actual derivative of the reconstructed cosine field, the sine field is
differentiable, and the single fifth-order `dB` equation holds, one
base-point Kaluza selector propagates throughout the patch. -/
theorem couplingSq_eq_three
    (P : FixedFourthOrderChannelPatch U)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hAdiff : ∀ x ∈ U, DifferentiableAt ℝ P.cosineComponent x)
    (hAderiv : ∀ x ∈ U,
      scalarFieldCoordinateFDeriv P.cosineComponent x =
        P.cosineDerivative x)
    (hBdiff : ∀ x ∈ U, DifferentiableAt ℝ P.sineComponent x)
    (hBeq : ∀ x ∈ U,
      sineCouplingPropagationEquation
        (scalarFieldCoordinateFDeriv P.sineComponent x)
        (P.effectiveOneForm x) (P.reflectedScalarCovector x)
        (P.cosineComponent x) (P.sineComponent x) = 0)
    {x0 : CurvatureCoordinateSpace4} (hx0 : x0 ∈ U)
    (hbase : P.cosineComponent x0 ^ 2 + P.sineComponent x0 ^ 2 = 3) :
    ∀ x ∈ U,
      P.cosineComponent x ^ 2 + P.sineComponent x ^ 2 = 3 := by
  apply couplingSq_eq_three_of_detectorPhaseEquations_on_openConvex
    U hUopen hUconvex P.cosineComponent P.sineComponent
    P.effectiveOneForm P.reflectedScalarCovector hAdiff hBdiff
  · intro x hx
    rw [hAderiv x hx]
    exact P.cosinePhaseEquation x hx
  · exact hBeq
  · exact hx0
  · exact hbase

end FixedFourthOrderChannelPatch

end RainichKaluza
