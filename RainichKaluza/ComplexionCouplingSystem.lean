import RainichKaluza.DualityComplexionDerivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Simultaneous recovery of complexion rate and EMD coupling

After a seed Maxwell two-form is chosen, evaluated differential channels are
linear in two unknown scalars: the infinitesimal duality complexion rate
`omega` and the EMD coupling `a`.  This file solves the resulting two-channel
system and identifies its exact degeneracy determinant.

The variables are scalar probe evaluations of the geometric forms.  Building
those probes from curvature and exterior calculus remains the geometric task.
-/

namespace RainichKaluza

/-- Determinant separating the complexion and scalar-coupling response
channels. -/
def complexionCouplingDet (z1 z2 y1 y2 : ℝ) : ℝ :=
  z1 * y2 - z2 * y1

/-- Reconstructed complexion rate from two evaluated channels. -/
noncomputable def complexionRateFromChannels
    (x1 x2 z1 z2 y1 y2 : ℝ) : ℝ :=
  (x1 * y2 - x2 * y1) / complexionCouplingDet z1 z2 y1 y2

/-- Reconstructed EMD coupling from two evaluated channels.  The factor two
matches equations whose scalar source occurs as `(a/2)Y`. -/
noncomputable def couplingFromComplexionChannels
    (x1 x2 z1 z2 y1 y2 : ℝ) : ℝ :=
  2 * (z1 * x2 - z2 * x1) / complexionCouplingDet z1 z2 y1 y2

/-- The channel equations determine the numerator of the complexion rate. -/
theorem complexionRate_channel_numerator
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    x1 * y2 - x2 * y1 =
      omega * complexionCouplingDet z1 z2 y1 y2 := by
  rw [h1, h2]
  unfold complexionCouplingDet
  ring

/-- The channel equations determine the numerator of the EMD coupling. -/
theorem coupling_channel_numerator
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    2 * (z1 * x2 - z2 * x1) =
      a * complexionCouplingDet z1 z2 y1 y2 := by
  rw [h1, h2]
  unfold complexionCouplingDet
  ring

/-- A nonzero channel determinant recovers the complexion rate exactly. -/
theorem complexionRateFromChannels_eq
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    complexionRateFromChannels x1 x2 z1 z2 y1 y2 = omega := by
  unfold complexionRateFromChannels
  rw [complexionRate_channel_numerator x1 x2 z1 z2 y1 y2 omega a h1 h2]
  field_simp [hdet]

/-- A nonzero channel determinant recovers the EMD coupling exactly. -/
theorem couplingFromComplexionChannels_eq
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 = a := by
  unfold couplingFromComplexionChannels
  rw [coupling_channel_numerator x1 x2 z1 z2 y1 y2 omega a h1 h2]
  field_simp [hdet]

/-- On the nondegenerate two-channel branch, the pair `(omega,a)` is unique. -/
theorem complexion_coupling_pair_unique
    (x1 x2 z1 z2 y1 y2 omega a omega' a' : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2)
    (h1' : x1 = omega' * z1 + (a' / 2) * y1)
    (h2' : x2 = omega' * z2 + (a' / 2) * y2) :
    omega = omega' ∧ a = a' := by
  constructor
  · rw [← complexionRateFromChannels_eq x1 x2 z1 z2 y1 y2 omega a
      hdet h1 h2]
    exact complexionRateFromChannels_eq x1 x2 z1 z2 y1 y2 omega' a'
      hdet h1' h2'
  · rw [← couplingFromComplexionChannels_eq x1 x2 z1 z2 y1 y2 omega a
      hdet h1 h2]
    exact couplingFromComplexionChannels_eq x1 x2 z1 z2 y1 y2 omega' a'
      hdet h1' h2'

/-- Reversing the scalar source orientation preserves the reconstructed
complexion rate. -/
theorem complexionRateFromChannels_neg_scalarSource
    (x1 x2 z1 z2 y1 y2 : ℝ) :
    complexionRateFromChannels x1 x2 z1 z2 (-y1) (-y2) =
      complexionRateFromChannels x1 x2 z1 z2 y1 y2 := by
  unfold complexionRateFromChannels complexionCouplingDet
  have hnum : x1 * -y2 - x2 * -y1 = -(x1 * y2 - x2 * y1) := by ring
  have hden : z1 * -y2 - z2 * -y1 = -(z1 * y2 - z2 * y1) := by ring
  calc
    (x1 * -y2 - x2 * -y1) / (z1 * -y2 - z2 * -y1) =
        (-(x1 * y2 - x2 * y1)) / (-(z1 * y2 - z2 * y1)) := by
      rw [hnum, hden]
    _ = (x1 * y2 - x2 * y1) / (z1 * y2 - z2 * y1) :=
      neg_div_neg_eq _ _

/-- Reversing the scalar source orientation reverses the reconstructed EMD
coupling, as required by `(v,a)↦(-v,-a)`. -/
theorem couplingFromComplexionChannels_neg_scalarSource
    (x1 x2 z1 z2 y1 y2 : ℝ) :
    couplingFromComplexionChannels x1 x2 z1 z2 (-y1) (-y2) =
      -couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingFromComplexionChannels complexionCouplingDet
  have hden : z1 * -y2 - z2 * -y1 = -(z1 * y2 - z2 * y1) := by ring
  calc
    2 * (z1 * x2 - z2 * x1) / (z1 * -y2 - z2 * -y1) =
        2 * (z1 * x2 - z2 * x1) / (-(z1 * y2 - z2 * y1)) := by
      rw [hden]
    _ = -(2 * (z1 * x2 - z2 * x1) / (z1 * y2 - z2 * y1)) := by
      rw [div_neg_eq_neg_div]

/-- A variable duality transition shifts each evaluated differential channel
by its transition rate times the corresponding complexion-response channel.
On the nondegenerate branch, the reconstructed raw complexion rate therefore
acquires exactly that transition rate. -/
theorem complexionRateFromChannels_gauge_shift
    (x1 x2 z1 z2 y1 y2 tau : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    complexionRateFromChannels (x1 + tau * z1) (x2 + tau * z2)
        z1 z2 y1 y2 =
      complexionRateFromChannels x1 x2 z1 z2 y1 y2 + tau := by
  unfold complexionRateFromChannels complexionCouplingDet at *
  field_simp [hdet]
  ring

/-- The simultaneously reconstructed EMD coupling is invariant under the
same variable-duality channel shift. -/
theorem couplingFromComplexionChannels_gauge_invariant
    (x1 x2 z1 z2 y1 y2 tau : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    couplingFromComplexionChannels (x1 + tau * z1) (x2 + tau * z2)
        z1 z2 y1 y2 =
      couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingFromComplexionChannels complexionCouplingDet at *
  field_simp [hdet]
  ring

/-- Gauge-corrected complexion reconstructed from two evaluated channels. -/
noncomputable def gaugeCorrectedComplexionRateFromChannels
    (x1 x2 z1 z2 y1 y2 connection : ℝ) : ℝ :=
  gaugeCorrectedComplexionRate
    (complexionRateFromChannels x1 x2 z1 z2 y1 y2) connection

/-- **Overlap-invariant channel theorem.** If a variable duality transition
shifts both the evaluated differential channels and the local connection by
the same rate, the corrected reconstructed complexion is unchanged. -/
theorem gaugeCorrectedComplexionRateFromChannels_invariant
    (x1 x2 z1 z2 y1 y2 connection tau : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    gaugeCorrectedComplexionRateFromChannels
        (x1 + tau * z1) (x2 + tau * z2) z1 z2 y1 y2
        (connection + tau) =
      gaugeCorrectedComplexionRateFromChannels
        x1 x2 z1 z2 y1 y2 connection := by
  unfold gaugeCorrectedComplexionRateFromChannels
  rw [complexionRateFromChannels_gauge_shift x1 x2 z1 z2 y1 y2 tau hdet]
  exact gaugeCorrectedComplexionRate_invariant
    (complexionRateFromChannels x1 x2 z1 z2 y1 y2) connection tau

end RainichKaluza
