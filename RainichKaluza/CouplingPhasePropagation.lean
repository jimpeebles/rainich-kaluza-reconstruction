import RainichKaluza.GeometricCouplingDetector
import Mathlib.Tactic.Ring

/-!
# Coupling phase propagation

The fourth-order detector reconstructs the double-angle components

`A = a (c² - s²)`, `B = a (2 c s)`

and its next-order equation encodes the phase law `dA = -2 B omega`.  This
file supplies the complementary product-rule derivative of `B`, packages the
proposed propagation equation

`dB = 2 A (eta - (B / 2) Jv)`,

and proves that the two phase laws make the product-rule derivative of
`A² + B²` vanish.

These are pointwise identities between prescribed first-jet covectors.  They
do not yet construct local phase or matter fields, prove that the detector
outputs are differentiable, or establish the EMD converse.
-/

namespace RainichKaluza

/-- Product-rule derivative of the double-angle sine component
`B = a (2 c s)` when the physical coupling `a` is constant. -/
def doubleAngleSineFirstDerivative
    (a c s : ℝ) (dc ds : OneForm4) : OneForm4 :=
  (2 * a * s) • dc + (2 * a * c) • ds

/-- The unit-circle phase equations turn the product-rule derivative of
`B = a (2 c s)` into `dB = 2 A omega`, where
`A = a (c² - s²)`. -/
theorem doubleAngleSineFirstDerivative_eq
    (a c s : ℝ) (dc ds omega : OneForm4)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega) :
    doubleAngleSineFirstDerivative a c s dc ds =
      (2 * (a * (c ^ 2 - s ^ 2))) • omega := by
  rw [hdc, hds]
  funext i
  simp [doubleAngleSineFirstDerivative]
  ring

/-- Product-rule first derivative of the reconstructed coupling square
`A² + B²`. -/
def couplingSqFirstDerivative
    (A B : ℝ) (dA dB : OneForm4) : OneForm4 :=
  (2 * A) • dA + (2 * B) • dB

/-- **Phase-law cancellation.**  The complementary laws
`dA = -2 B omega` and `dB = 2 A omega` force the product-rule derivative of
`A² + B²` to vanish. -/
theorem couplingSqFirstDerivative_eq_zero_of_phaseLaws
    (A B : ℝ) (dA dB omega : OneForm4)
    (hdA : dA = (-2 * B) • omega)
    (hdB : dB = (2 * A) • omega) :
    couplingSqFirstDerivative A B dA dB = 0 := by
  rw [hdA, hdB]
  funext i
  simp [couplingSqFirstDerivative]
  ring

/-- The double-angle product-rule derivatives satisfy the coupling-square
cancellation directly. -/
theorem couplingSqFirstDerivative_doubleAngle_eq_zero
    (a c s : ℝ) (dc ds omega : OneForm4)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega) :
    couplingSqFirstDerivative
        (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s))
        (doubleAngleCosineFirstDerivative a c s dc ds)
        (doubleAngleSineFirstDerivative a c s dc ds) = 0 := by
  apply couplingSqFirstDerivative_eq_zero_of_phaseLaws
      (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s)) _ _ omega
  · exact doubleAngleCosineFirstDerivative_eq a c s dc ds omega hdc hds
  · exact doubleAngleSineFirstDerivative_eq a c s dc ds omega hdc hds

/-- Recover the physical phase one-form from the effective first-order
channel `eta = omega + (B / 2) Jv`. -/
noncomputable def phaseOneFormFromEffectiveChannel
    (eta Jv : OneForm4) (B : ℝ) : OneForm4 :=
  eta - (B / 2) • Jv

/-- Subtracting the channel shear recovers the original phase one-form. -/
theorem phaseOneFormFromEffectiveChannel_eq
    (omega Jv : OneForm4) (B : ℝ) :
    phaseOneFormFromEffectiveChannel
        (effectiveComplexionOneForm omega Jv B) Jv B = omega := by
  funext i
  simp [phaseOneFormFromEffectiveChannel, effectiveComplexionOneForm]

/-- Reversing the scalar orientation together with the signed sine component
does not change the recovered physical phase one-form. -/
theorem phaseOneFormFromEffectiveChannel_neg_scalar
    (eta Jv : OneForm4) (B : ℝ) :
    phaseOneFormFromEffectiveChannel eta (-Jv) (-B) =
      phaseOneFormFromEffectiveChannel eta Jv B := by
  funext i
  simp [phaseOneFormFromEffectiveChannel]
  ring

/-- Residual of the proposed sine-component propagation law
`dB = 2 A (eta - (B / 2) Jv)`. -/
noncomputable def sineCouplingPropagationEquation
    (dB eta Jv : OneForm4) (A B : ℝ) : OneForm4 :=
  dB - (2 * A) • phaseOneFormFromEffectiveChannel eta Jv B

/-- Vanishing of the propagation residual is exactly the physical phase law
for `dB`. -/
theorem sineCouplingPropagationEquation_eq_zero_iff
    (dB eta Jv : OneForm4) (A B : ℝ) :
    sineCouplingPropagationEquation dB eta Jv A B = 0 ↔
      dB = (2 * A) • phaseOneFormFromEffectiveChannel eta Jv B := by
  unfold sineCouplingPropagationEquation
  exact sub_eq_zero

/-- The existing fourth-order constancy equation is exactly the residual of
the complementary phase law `dA = -2 B (eta - (B / 2) Jv)`. -/
theorem nextOrderSineCouplingEquation_eq_phaseLawResidual
    (dA eta Jv : OneForm4) (B : ℝ) :
    nextOrderSineCouplingEquation dA eta Jv B =
      dA - (-2 * B) • phaseOneFormFromEffectiveChannel eta Jv B := by
  funext i
  simp [nextOrderSineCouplingEquation, phaseOneFormFromEffectiveChannel]
  ring

/-- **Detector-to-propagation cancellation.**  The existing fourth-order
constancy equation and the new sine propagation equation together force the
product-rule derivative of the reconstructed squared coupling to vanish. -/
theorem couplingSqFirstDerivative_eq_zero_of_detectorPhaseEquations
    (A B : ℝ) (dA dB eta Jv : OneForm4)
    (hA : nextOrderSineCouplingEquation dA eta Jv B = 0)
    (hB : sineCouplingPropagationEquation dB eta Jv A B = 0) :
    couplingSqFirstDerivative A B dA dB = 0 := by
  apply couplingSqFirstDerivative_eq_zero_of_phaseLaws A B dA dB
      (phaseOneFormFromEffectiveChannel eta Jv B)
  · apply sub_eq_zero.mp
    rw [← nextOrderSineCouplingEquation_eq_phaseLawResidual]
    exact hA
  · exact
      (sineCouplingPropagationEquation_eq_zero_iff dB eta Jv A B).mp hB

/-- The propagation residual is covariant under reversal of scalar
orientation and both signed double-angle components. -/
theorem sineCouplingPropagationEquation_neg_scalar
    (dB eta Jv : OneForm4) (A B : ℝ) :
    sineCouplingPropagationEquation (-dB) eta (-Jv) (-A) (-B) =
      -sineCouplingPropagationEquation dB eta Jv A B := by
  funext i
  simp [sineCouplingPropagationEquation,
    phaseOneFormFromEffectiveChannel]
  ring

/-- The product-rule derivative of `A² + B²` is unchanged when both signed
components and both of their derivative covectors reverse. -/
theorem couplingSqFirstDerivative_neg_components
    (A B : ℝ) (dA dB : OneForm4) :
    couplingSqFirstDerivative (-A) (-B) (-dA) (-dB) =
      couplingSqFirstDerivative A B dA dB := by
  funext i
  simp [couplingSqFirstDerivative]

end RainichKaluza
