import RainichKaluza.PrincipalPlaneFrame
import RainichKaluza.ReconstructionEquation
import RainichKaluza.RankOneEndomorphism

/-!
# Physical scalar identifiability from the Ricci reconstruction equation

This file extracts the physical scalar covector directly along Ricci
eigendirections.  Pairing the coordinate-free reconstruction equation with a
normalized Ricci eigenvector forces that scalar component's magnitude.  On a
protected Maxwell root, the same identity forces the component to vanish away
from the explicit resonance `2 lambda = traceV`.

Together these statements isolate the remaining detector entrance work as a
finite spectral-basis/projector composition, rather than an additional
physical amplitude or relative-sign assumption.
-/

namespace RainichKaluza

open LinearMap (BilinForm)
open Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Physical rank-one decomposition implies reconstruction.** If the Ricci
endomorphism splits into a Maxwell part with scalar square and the physical
rank-one scalar part, whose rank-one trace coefficient is `traceV`, then the
scalar reconstruction equation follows automatically.  This is the exact
algebraic interface a choice-independent EMD Einstein/Ricci witness must
supply. -/
theorem reconstructionEquation_of_rankOneRicciDecomposition
    (R S : Module.End ℝ E) (v : E →ₗ[ℝ] ℝ) (vSharp : E)
    (traceV qSq : ℝ)
    (hR : R = S + rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp))
    (hS : S * S = qSq • (1 : Module.End ℝ E))
    (htrace : v ((2 : ℝ)⁻¹ • vSharp) = traceV) :
    let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
    R * V + V * R - traceV • V =
      R * R - qSq • (1 : Module.End ℝ E) := by
  let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
  have hV : V * V = traceV • V := by
    change rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp) *
        rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp) =
      traceV • rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
    rw [rankOneEndomorphism_sq, htrace]
  exact reconstructionEquation_of_eq_add R S V traceV qSq hR hS hV

/-- **Eigenvector pairing identity.** Pairing the reconstruction equation
with a normalized eigenvector of a metric-self-adjoint Ricci endomorphism
forces the corresponding diagonal scalar contribution. -/
theorem reconstructionEquation_eigenvector_pairing
    (g : BilinForm ℝ E) (R V : Module.End ℝ E)
    (traceV qSq lambda epsilon : ℝ) (e : E)
    (hself : MetricSelfAdjoint g R)
    (heigen : R e = lambda • e)
    (hnorm : g e e = epsilon)
    (hrecon : R * V + V * R - traceV • V =
      R * R - qSq • (1 : Module.End ℝ E)) :
    (2 * lambda - traceV) * g e (V e) =
      (lambda ^ 2 - qSq) * epsilon := by
  have hRV : g e (R (V e)) = lambda * g e (V e) := by
    rw [← hself e (V e), heigen]
    simp
  have hVR : g e (V (R e)) = lambda * g e (V e) := by
    rw [heigen, map_smul]
    simp
  have hRR : g e (R (R e)) = lambda ^ 2 * epsilon := by
    rw [heigen, map_smul, heigen]
    simp only [LinearMap.BilinForm.smul_right, hnorm]
    ring
  have hpair := congrArg (fun w : E => g e w)
    (LinearMap.congr_fun hrecon e)
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_right] at hpair
  rw [hRV, hVR, hRR, hnorm] at hpair
  linarith

/-- The mixed rank-one scalar tensor pairs with an eigenvector as one half of
the square of the scalar covector component. -/
theorem metricPairing_rankOneScalarContribution
    (g : BilinForm ℝ E) (v : E →ₗ[ℝ] ℝ) (vSharp e : E)
    (hdual : ∀ y, g y vSharp = v y) :
    g e (rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp) e) =
      (v e) ^ 2 / 2 := by
  simp only [rankOneEndomorphism_apply, LinearMap.BilinForm.smul_right,
    smul_smul, hdual]
  ring

/-- **Physical scalar eigencomponent identity.** For
`V=(1/2) vSharp tensor v`, the Ricci reconstruction equation fixes the square
of `v` evaluated on every normalized Ricci eigendirection. -/
theorem reconstructionEquation_scalarCovector_eigencomponent
    (g : BilinForm ℝ E) (R : Module.End ℝ E)
    (v : E →ₗ[ℝ] ℝ) (vSharp : E)
    (traceV qSq lambda epsilon : ℝ) (e : E)
    (hdual : ∀ y, g y vSharp = v y)
    (hself : MetricSelfAdjoint g R)
    (heigen : R e = lambda • e)
    (hnorm : g e e = epsilon)
    (hrecon :
      let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
      R * V + V * R - traceV • V =
        R * R - qSq • (1 : Module.End ℝ E)) :
    (2 * lambda - traceV) * ((v e) ^ 2 / 2) =
      (lambda ^ 2 - qSq) * epsilon := by
  let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
  have hpair := reconstructionEquation_eigenvector_pairing
    g R V traceV qSq lambda epsilon e hself heigen hnorm hrecon
  rw [metricPairing_rankOneScalarContribution g v vSharp e hdual] at hpair
  exact hpair

/-- **Protected roots carry no physical scalar component.** If a Ricci
eigenvalue also obeys the Maxwell square polynomial and is not in the explicit
trace resonance, the physical scalar covector annihilates that eigendirection.
-/
theorem scalarCovector_vanishes_on_protectedEigenvector
    (g : BilinForm ℝ E) (R : Module.End ℝ E)
    (v : E →ₗ[ℝ] ℝ) (vSharp : E)
    (traceV qSq lambda epsilon : ℝ) (e : E)
    (hdual : ∀ y, g y vSharp = v y)
    (hself : MetricSelfAdjoint g R)
    (heigen : R e = lambda • e)
    (hnorm : g e e = epsilon)
    (hprotected : lambda ^ 2 = qSq)
    (hnonresonance : 2 * lambda ≠ traceV)
    (hrecon :
      let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
      R * V + V * R - traceV • V =
        R * R - qSq • (1 : Module.End ℝ E)) :
    v e = 0 := by
  have hcomponent := reconstructionEquation_scalarCovector_eigencomponent
    g R v vSharp traceV qSq lambda epsilon e hdual hself heigen hnorm hrecon
  have hcoeff : 2 * lambda - traceV ≠ 0 := sub_ne_zero.mpr hnonresonance
  rw [hprotected] at hcomponent
  have hsquare : (v e) ^ 2 = 0 := by
    have : (v e) ^ 2 / 2 = 0 :=
      (mul_eq_zero.mp (by simpa using hcomponent)).resolve_left hcoeff
    linarith
  exact sq_eq_zero_iff.mp hsquare

/-- **Complementary Ricci eigencomponents have the reconstructed
amplitudes.** On the two nonprotected roots `a,b`, with `traceV=a+b`, the
physical scalar component magnitudes are exactly the detector's
signature-adjusted square roots. -/
theorem scalarCovector_complementaryEigencomponents_sqrt_eq_abs
    (g : BilinForm ℝ E) (R : Module.End ℝ E)
    (v : E →ₗ[ℝ] ℝ) (vSharp : E)
    (a b qSq epsilonA epsilonB : ℝ) (eA eB : E)
    (hab : a ≠ b)
    (hdual : ∀ y, g y vSharp = v y)
    (hself : MetricSelfAdjoint g R)
    (heigenA : R eA = a • eA)
    (heigenB : R eB = b • eB)
    (hnormA : g eA eA = epsilonA)
    (hnormB : g eB eB = epsilonB)
    (hrecon :
      let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
      R * V + V * R - (a + b) • V =
        R * R - qSq • (1 : Module.End ℝ E)) :
    Real.sqrt (2 * epsilonA * reconstructedDiagonalA a b qSq) =
        |v eA| ∧
      Real.sqrt (2 * epsilonB * reconstructedDiagonalB a b qSq) =
        |v eB| := by
  have hA := reconstructionEquation_scalarCovector_eigencomponent
    g R v vSharp (a + b) qSq a epsilonA eA hdual hself heigenA hnormA hrecon
  have hB := reconstructionEquation_scalarCovector_eigencomponent
    g R v vSharp (a + b) qSq b epsilonB eB hdual hself heigenB hnormB hrecon
  have hdenA : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hdenB : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hargA :
      2 * epsilonA * reconstructedDiagonalA a b qSq = (v eA) ^ 2 := by
    unfold reconstructedDiagonalA
    field_simp [hdenA]
    nlinarith
  have hargB :
      2 * epsilonB * reconstructedDiagonalB a b qSq = (v eB) ^ 2 := by
    unfold reconstructedDiagonalB
    field_simp [hdenB]
    nlinarith
  constructor
  · rw [hargA, Real.sqrt_sq_eq_abs]
  · rw [hargB, Real.sqrt_sq_eq_abs]

/-- **Two-line support from a pseudo-orthonormal eigenbasis.** If a covector
annihilates the two protected basis directions, it is exactly the sum of its
metric-dual components on the two complementary directions. This is the
linear-algebra bridge from protected-root vanishing to membership in the two
rank-one scalar eigenlines. -/
theorem covector_eq_complementaryMetricDualComponents
    (g : BilinForm ℝ E) (basis : Basis (Fin 4) ℝ E)
    (epsilon : Fin 4 → ℝ)
    (horth : ∀ i j, g (basis i) (basis j) =
      if i = j then epsilon i else 0)
    (hepsilon : ∀ i, (epsilon i) ^ 2 = 1)
    (v : E →ₗ[ℝ] ℝ)
    (hprotectedMinus : v (basis 1) = 0)
    (hprotectedPlus : v (basis 3) = 0) :
    v = (epsilon 0 * v (basis 0)) • g (basis 0) +
      (epsilon 2 * v (basis 2)) • g (basis 2) := by
  have hepsilon_mul (i : Fin 4) (x : ℝ) :
      epsilon i * x * epsilon i = x := by
    calc
      epsilon i * x * epsilon i = (epsilon i) ^ 2 * x := by ring
      _ = x := by rw [hepsilon i]; ring
  apply basis.ext
  intro i
  fin_cases i <;>
    simp [horth, hprotectedMinus, hprotectedPlus, hepsilon_mul]

/-- Orient a normalized representative of a rank-one range so that its
metric-dual multiple uses the nonnegative amplitude `|c|`. -/
theorem exists_orientedRangeRepresentative_abs_smul_metricDual_eq
    (g : BilinForm ℝ E) (P : Module.End ℝ E) (e : P.range)
    (sigma c : ℝ) (hnorm : g (e : E) (e : E) = sigma) :
    ∃ oriented : P.range,
      g (oriented : E) (oriented : E) = sigma ∧
      |c| • g (oriented : E) = c • g (e : E) := by
  by_cases hc : 0 ≤ c
  · exact ⟨e, hnorm, by rw [abs_of_nonneg hc]⟩
  · let oriented : P.range := -e
    refine ⟨oriented, ?_, ?_⟩
    · simpa [oriented] using hnorm
    · have hcNeg : c < 0 := lt_of_not_ge hc
      rw [abs_of_neg hcNeg]
      simp [oriented]

/-- **Finite probes recover any physically supported scalar covector.** If a
physical covector is supported on normalized representatives of two rank-one
Lorentzian spectral lines, and `ampA,ampB` are the absolute component
magnitudes, then the concrete project-and-normalize detector list contains
that covector up to the unavoidable global sign.

This is the complete composition of range membership, amplitude magnitude,
finite probe selection, and relative-sign enumeration. -/
theorem exists_projectedProbeScalarBranch_eq_or_neg_of_physicalSupport
    (g : BilinForm ℝ E) (P Q : Module.End ℝ E)
    (hrankP : finrank ℝ P.range = 1)
    (hrankQ : finrank ℝ Q.range = 1)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (u w : E)
    (hPu : g (P u) (P u) < 0)
    (hQw : 0 < g (Q w) (Q w))
    (eA : P.range) (eB : Q.range)
    (hnormA : g (eA : E) (eA : E) = -1)
    (hnormB : g (eB : E) (eB : E) = 1)
    (v : E →ₗ[ℝ] ℝ) (cA cB ampA ampB : ℝ)
    (hv : v = cA • g (eA : E) + cB • g (eB : E))
    (hampA : ampA = |cA|) (hampB : ampB = |cB|) :
    ∃ relativeMinus : Bool,
      (if relativeMinus then
          ampA • g (normalizeTimelike g (P u)) -
            ampB • g (normalizeSpacelike g (Q w))
        else
          ampA • g (normalizeTimelike g (P u)) +
            ampB • g (normalizeSpacelike g (Q w))) = v ∨
        (if relativeMinus then
            ampA • g (normalizeTimelike g (P u)) -
              ampB • g (normalizeSpacelike g (Q w))
          else
            ampA • g (normalizeTimelike g (P u)) +
              ampB • g (normalizeSpacelike g (Q w))) = -v := by
  obtain ⟨orientedA, hnormOrientedA, horientA⟩ :=
    exists_orientedRangeRepresentative_abs_smul_metricDual_eq
      g P eA (-1) cA hnormA
  obtain ⟨orientedB, hnormOrientedB, horientB⟩ :=
    exists_orientedRangeRepresentative_abs_smul_metricDual_eq
      g Q eB 1 cB hnormB
  have horientedANe : (orientedA : E) ≠ 0 := by
    intro hzero
    rw [hzero, LinearMap.BilinForm.zero_left] at hnormOrientedA
    norm_num at hnormOrientedA
  have horientedBNe : (orientedB : E) ≠ 0 := by
    intro hzero
    rw [hzero, LinearMap.BilinForm.zero_left] at hnormOrientedB
    norm_num at hnormOrientedB
  obtain ⟨relativeMinus, hbranch⟩ :=
    exists_relativeSignMetricDualCombination_eq_or_neg_of_projectedProbes
      g P Q hrankP hrankQ hP hQ u w hPu hQw
      orientedA orientedB horientedANe horientedBNe
      hnormOrientedA hnormOrientedB ampA ampB
  refine ⟨relativeMinus, ?_⟩
  have htarget :
      ampA • g (orientedA : E) + ampB • g (orientedB : E) = v := by
    rw [hampA, hampB, horientA, horientB, hv]
  rcases hbranch with hbranch | hbranch
  · exact Or.inl (hbranch.trans htarget)
  · exact Or.inr (hbranch.trans (congrArg Neg.neg htarget))

/-- **Generic spectral-frame physical scalar entrance.** In a
pseudo-orthonormal Ricci eigenbasis with complementary roots `a,b` and
protected roots `-q,+q`, the physical EMD scalar rank-one contribution and the
Maxwell square law imply that the finite projected-probe scalar list contains
the physical covector up to global sign.

The only exclusions beyond simple roots and nonzero probe signs are the two
explicit resonances `a+b=±2q`. No physical component, amplitude, probe, or
relative-sign choice is supplied to the conclusion. -/
theorem exists_projectedProbeScalarBranch_eq_or_neg_of_reconstructionEquation
    (g : BilinForm ℝ E) (R : Module.End ℝ E)
    (v : E →ₗ[ℝ] ℝ) (vSharp : E)
    (basis : Basis (Fin 4) ℝ E)
    (a b q qSq : ℝ)
    (horth : ∀ i j, g (basis i) (basis j) =
      if i = j then minkowskiSign i else 0)
    (hself : MetricSelfAdjoint g R)
    (heigenA : R (basis 0) = a • basis 0)
    (heigenMinus : R (basis 1) = (-q) • basis 1)
    (heigenB : R (basis 2) = b • basis 2)
    (heigenPlus : R (basis 3) = q • basis 3)
    (hab : a ≠ b) (hqSq : q ^ 2 = qSq)
    (hminusNonresonance : -(2 * q) ≠ a + b)
    (hplusNonresonance : 2 * q ≠ a + b)
    (hdual : ∀ y, g y vSharp = v y)
    (hrecon :
      let V := rankOneEndomorphism v ((2 : ℝ)⁻¹ • vSharp)
      R * V + V * R - (a + b) • V =
        R * R - qSq • (1 : Module.End ℝ E))
    (P Q : Module.End ℝ E)
    (hrankP : finrank ℝ P.range = 1)
    (hrankQ : finrank ℝ Q.range = 1)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (hPA : P (basis 0) = basis 0)
    (hQB : Q (basis 2) = basis 2)
    (u w : E)
    (hPu : g (P u) (P u) < 0)
    (hQw : 0 < g (Q w) (Q w)) :
    ∃ relativeMinus : Bool,
      (if relativeMinus then
          Real.sqrt (2 * (-1 : ℝ) * reconstructedDiagonalA a b qSq) •
              g (normalizeTimelike g (P u)) -
            Real.sqrt (2 * (1 : ℝ) * reconstructedDiagonalB a b qSq) •
              g (normalizeSpacelike g (Q w))
        else
          Real.sqrt (2 * (-1 : ℝ) * reconstructedDiagonalA a b qSq) •
              g (normalizeTimelike g (P u)) +
            Real.sqrt (2 * (1 : ℝ) * reconstructedDiagonalB a b qSq) •
              g (normalizeSpacelike g (Q w))) = v ∨
        (if relativeMinus then
            Real.sqrt (2 * (-1 : ℝ) * reconstructedDiagonalA a b qSq) •
                g (normalizeTimelike g (P u)) -
              Real.sqrt (2 * (1 : ℝ) * reconstructedDiagonalB a b qSq) •
                g (normalizeSpacelike g (Q w))
          else
            Real.sqrt (2 * (-1 : ℝ) * reconstructedDiagonalA a b qSq) •
                g (normalizeTimelike g (P u)) +
              Real.sqrt (2 * (1 : ℝ) * reconstructedDiagonalB a b qSq) •
                g (normalizeSpacelike g (Q w))) = -v := by
  have hnormA : g (basis 0) (basis 0) = -1 := by
    simpa [minkowskiSign] using horth 0 0
  have hnormMinus : g (basis 1) (basis 1) = 1 := by
    simpa [minkowskiSign] using horth 1 1
  have hnormB : g (basis 2) (basis 2) = 1 := by
    simpa [minkowskiSign] using horth 2 2
  have hnormPlus : g (basis 3) (basis 3) = 1 := by
    simpa [minkowskiSign] using horth 3 3
  have hminusProtected : (-q) ^ 2 = qSq := by nlinarith
  have hminusNonresonance' : 2 * (-q) ≠ a + b := by
    intro hresonance
    apply hminusNonresonance
    calc
      -(2 * q) = 2 * (-q) := by ring
      _ = a + b := hresonance
  have hzeroMinus : v (basis 1) = 0 :=
    scalarCovector_vanishes_on_protectedEigenvector
      g R v vSharp (a + b) qSq (-q) 1 (basis 1)
      hdual hself heigenMinus hnormMinus hminusProtected
      hminusNonresonance' hrecon
  have hzeroPlus : v (basis 3) = 0 :=
    scalarCovector_vanishes_on_protectedEigenvector
      g R v vSharp (a + b) qSq q 1 (basis 3)
      hdual hself heigenPlus hnormPlus hqSq
      hplusNonresonance hrecon
  have hepsilon : ∀ i, (minkowskiSign i) ^ 2 = 1 := by
    intro i
    fin_cases i <;> norm_num [minkowskiSign]
  have hsupport := covector_eq_complementaryMetricDualComponents
    g basis minkowskiSign horth hepsilon v hzeroMinus hzeroPlus
  have hamplitudes :=
    scalarCovector_complementaryEigencomponents_sqrt_eq_abs
      g R v vSharp a b qSq (-1) 1 (basis 0) (basis 2)
      hab hdual hself heigenA heigenB hnormA hnormB hrecon
  let eA : P.range := ⟨basis 0, ⟨basis 0, hPA⟩⟩
  let eB : Q.range := ⟨basis 2, ⟨basis 2, hQB⟩⟩
  apply exists_projectedProbeScalarBranch_eq_or_neg_of_physicalSupport
    g P Q hrankP hrankQ hP hQ u w hPu hQw eA eB
    (by simpa [eA] using hnormA) (by simpa [eB] using hnormB)
    v (-v (basis 0)) (v (basis 2))
    (Real.sqrt (2 * (-1 : ℝ) * reconstructedDiagonalA a b qSq))
    (Real.sqrt (2 * (1 : ℝ) * reconstructedDiagonalB a b qSq))
  · simpa [eA, eB, minkowskiSign] using hsupport
  · simpa only [abs_neg] using hamplitudes.1
  · exact hamplitudes.2

end RainichKaluza
