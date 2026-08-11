import RainichKaluza.PrincipalPlaneFrame
import RainichKaluza.ProtectedEigenspaces
import RainichKaluza.ProtectedFactorization
import RainichKaluza.AlgebraicFingerprint
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Four-dimensional algebraic entrance to the Rainich--Kaluza factorization

The repository already proves two ingredients that had not yet been composed:

* in dimension four, a tracefree non-null square-law residual has rank-two
  positive and negative polynomial projector ranges;
* a rank-one perturbation preserves an eigenvalue whenever its eigenspace
  contains two linearly independent vectors.

This file closes that seam.  It extracts independent pairs from both Maxwell
projector ranges, proves that they are `+q` and `-q` eigenvectors of the
residual, applies rank-one protection, and turns the surviving eigenvectors
into roots of the actual endomorphism characteristic polynomial.  An explicit
`HasCharacteristicData` bridge then transfers those roots to the repository's
quartic coefficient package and invokes the already proved protected-pair
factorization theorem.

No exterior-algebra multiplicity theorem is required at this stage: in four
dimensions the two multiplicities follow from the square law, trace zero, and
`q != 0`.  Those hypotheses are still necessary; the algebraic false
positives documented elsewhere do not satisfy the complete entrance package.
-/

namespace RainichKaluza

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A rank-two submodule contains two ambient linearly independent vectors.
The result packages their range membership so it can feed the protected-plane
argument without choosing a basis of the ambient space. -/
theorem exists_linearIndependent_pair_of_finrank_range_eq_two
    [FiniteDimensional ℝ V]
    (P : V →ₗ[ℝ] V) (hrank : finrank ℝ P.range = 2) :
    ∃ x y : V,
      LinearIndependent ℝ ![x, y] ∧ x ∈ P.range ∧ y ∈ P.range := by
  have hle : 2 ≤ finrank ℝ P.range := by omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hle
  have hvAmbient :
      LinearIndependent ℝ (fun i : Fin 2 => ((v i : P.range) : V)) :=
    hv.map' P.range.subtype (Submodule.ker_subtype P.range)
  refine ⟨v 0, v 1, ?_, (v 0).property, (v 1).property⟩
  convert hvAmbient using 1
  ext i
  fin_cases i <;> rfl

/-- The two rank-two Maxwell projector ranges provide independent `+q` and
`-q` eigenvector pairs for the unperturbed residual. -/
theorem exists_maxwellResidual_principal_eigenpairs
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0) :
    ∃ p₁ p₂ m₁ m₂ : V,
      LinearIndependent ℝ ![p₁, p₂] ∧
      LinearIndependent ℝ ![m₁, m₂] ∧
      S p₁ = q • p₁ ∧ S p₂ = q • p₂ ∧
      S m₁ = (-q) • m₁ ∧ S m₂ = (-q) • m₂ := by
  obtain ⟨hrankPlus, hrankMinus⟩ :=
    maxwellProjectors_finrank_range_eq_two S q hq hS hdim htrace
  obtain ⟨p₁, p₂, hp, hp₁mem, hp₂mem⟩ :=
    exists_linearIndependent_pair_of_finrank_range_eq_two
      (maxwellPlusProjector S q) hrankPlus
  obtain ⟨m₁, m₂, hm, hm₁mem, hm₂mem⟩ :=
    exists_linearIndependent_pair_of_finrank_range_eq_two
      (maxwellMinusProjector S q) hrankMinus
  have hplusId := maxwellPlusProjector_sq S q hq hS
  have hminusId := maxwellMinusProjector_sq S q hq hS
  have hp₁fix := projector_fixed_of_mem_range
    (maxwellPlusProjector S q) hplusId p₁ hp₁mem
  have hp₂fix := projector_fixed_of_mem_range
    (maxwellPlusProjector S q) hplusId p₂ hp₂mem
  have hm₁fix := projector_fixed_of_mem_range
    (maxwellMinusProjector S q) hminusId m₁ hm₁mem
  have hm₂fix := projector_fixed_of_mem_range
    (maxwellMinusProjector S q) hminusId m₂ hm₂mem
  exact ⟨p₁, p₂, m₁, m₂, hp, hm,
    maxwellResidual_apply_eq_smul_of_plus_fixed S q hq hS p₁ hp₁fix,
    maxwellResidual_apply_eq_smul_of_plus_fixed S q hq hS p₂ hp₂fix,
    maxwellResidual_apply_eq_neg_smul_of_minus_fixed S q hq hS m₁ hm₁fix,
    maxwellResidual_apply_eq_neg_smul_of_minus_fixed S q hq hS m₂ hm₂fix⟩

/-- **Four-dimensional protected-pair assembly.** Adding an arbitrary rank-one
endomorphism to a tracefree non-null Maxwell residual preserves a nonzero
`+q` eigenvector and a nonzero `-q` eigenvector.  The principal-plane
multiplicity hypotheses of the earlier abstract theorem are now consequences,
not inputs. -/
theorem exists_protected_opposite_eigenvectors_of_maxwellResidual
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0) :
    (∃ p : V, p ≠ 0 ∧
      (S + rankOneEndomorphism f x) p = q • p) ∧
    (∃ m : V, m ≠ 0 ∧
      (S + rankOneEndomorphism f x) m = (-q) • m) := by
  obtain ⟨p₁, p₂, m₁, m₂, hp, hm, hp₁, hp₂, hm₁, hm₂⟩ :=
    exists_maxwellResidual_principal_eigenpairs S q hq hS hdim htrace
  exact exists_protected_opposite_eigenvectors
    S f x q p₁ p₂ m₁ m₂ hp hm hp₁ hp₂ hm₁ hm₂

/-- The protected eigenvectors are roots of the actual characteristic
polynomial of the rank-one perturbed endomorphism. -/
theorem protected_opposite_isRoot_charpoly_of_maxwellResidual
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0) :
    (S + rankOneEndomorphism f x).charpoly.IsRoot q ∧
      (S + rankOneEndomorphism f x).charpoly.IsRoot (-q) := by
  obtain ⟨⟨p, hpne, hp⟩, ⟨m, hmne, hm⟩⟩ :=
    exists_protected_opposite_eigenvectors_of_maxwellResidual
      S f x q hq hS hdim htrace
  constructor
  · rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hp, hpne⟩
  · rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hm, hmne⟩

/-- Characteristic coefficients extracted from an actual four-dimensional
endomorphism, in the repository's sign convention
`z^4-e1*z^3+e2*z^2-e3*z+e4`. -/
noncomputable def CharacteristicData.ofEndomorphism
    [FiniteDimensional ℝ V]
    (R : V →ₗ[ℝ] V) : CharacteristicData where
  e1 := -R.charpoly.coeff 3
  e2 := R.charpoly.coeff 2
  e3 := -R.charpoly.coeff 1
  e4 := R.charpoly.coeff 0

/-- An endomorphism and a quartic coefficient package describe the same
characteristic polynomial when their evaluations agree at every scalar.  The
explicit relation prevents a silent sign-convention change between Mathlib's
`charpoly` and `CharacteristicData.monicQuartic`. -/
def HasCharacteristicData
    [FiniteDimensional ℝ V]
    (R : V →ₗ[ℝ] V) (d : CharacteristicData) : Prop :=
  ∀ z : ℝ, Polynomial.eval z R.charpoly = monicQuartic d z

/-- Every endomorphism of a four-dimensional real vector space has the
canonical characteristic data extracted above. -/
theorem hasCharacteristicData_ofEndomorphism
    [FiniteDimensional ℝ V]
    (R : V →ₗ[ℝ] V) (hdim : finrank ℝ V = 4) :
    HasCharacteristicData R (CharacteristicData.ofEndomorphism R) := by
  have hnat : R.charpoly.natDegree = 4 :=
    R.charpoly_natDegree.trans hdim
  have hlead : R.charpoly.coeff 4 = 1 := by
    have h := R.charpoly_monic.leadingCoeff
    rw [Polynomial.leadingCoeff, hnat] at h
    exact h
  intro z
  rw [Polynomial.eval_eq_sum_range, hnat]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [CharacteristicData.ofEndomorphism, monicQuartic, hlead]
  ring

/-- An actual characteristic root transfers through the explicit coefficient
bridge to a root of the encoded monic quartic. -/
theorem HasCharacteristicData.monicQuartic_eq_zero_of_isRoot
    [FiniteDimensional ℝ V]
    {R : V →ₗ[ℝ] V} {d : CharacteristicData}
    (hdata : HasCharacteristicData R d) {z : ℝ}
    (hroot : R.charpoly.IsRoot z) :
    monicQuartic d z = 0 := by
  rw [← hdata z]
  exact hroot

/-- **II-G1 characteristic factorization.** The characteristic polynomial of
the four-dimensional rank-one perturbation contains the protected factor
`z^2-q^2`; the complementary quadratic is fixed by the characteristic data.
This is the end-to-end assembly from the Maxwell square law to the advertised
quartic factorization. -/
theorem charpoly_factorization_of_maxwellResidual_add_rankOne
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (d : CharacteristicData)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hdata : HasCharacteristicData (S + rankOneEndomorphism f x) d) :
    ∀ z : ℝ,
      Polynomial.eval z (S + rankOneEndomorphism f x).charpoly =
        (z ^ 2 - q ^ 2) * (z ^ 2 - d.e1 * z + d.e2 + q ^ 2) := by
  obtain ⟨hplusRoot, hminusRoot⟩ :=
    protected_opposite_isRoot_charpoly_of_maxwellResidual
      S f x q hq hS hdim htrace
  have hplus := hdata.monicQuartic_eq_zero_of_isRoot hplusRoot
  have hminus := hdata.monicQuartic_eq_zero_of_isRoot hminusRoot
  intro z
  rw [hdata z]
  exact monicQuartic_factorization_of_opposite_roots
    d q z hq hplus hminus

/-- The characteristic coefficients of the perturbed endomorphism are exactly
the factorization coefficients forced by the protected pair. -/
theorem characteristicData_eq_from_maxwellResidual_add_rankOne
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (d : CharacteristicData)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hdata : HasCharacteristicData (S + rankOneEndomorphism f x) d) :
    d = CharacteristicData.fromFactorization
      { ricciTrace := d.e1
        qSq := q ^ 2
        residualConstant := -(d.e2 + q ^ 2) } := by
  obtain ⟨hplusRoot, hminusRoot⟩ :=
    protected_opposite_isRoot_charpoly_of_maxwellResidual
      S f x q hq hS hdim htrace
  exact characteristicData_eq_fromFactorization_of_opposite_roots d q hq
    (hdata.monicQuartic_eq_zero_of_isRoot hplusRoot)
    (hdata.monicQuartic_eq_zero_of_isRoot hminusRoot)

/-- Canonical-data specialization of the II-G1 factorization: no external
coefficient bridge is required. -/
theorem charpoly_factorization_of_maxwellResidual_add_rankOne_canonical
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0) :
    ∀ z : ℝ,
      Polynomial.eval z (S + rankOneEndomorphism f x).charpoly =
        (z ^ 2 - q ^ 2) *
          (z ^ 2 -
            (CharacteristicData.ofEndomorphism
              (S + rankOneEndomorphism f x)).e1 * z +
            (CharacteristicData.ofEndomorphism
              (S + rankOneEndomorphism f x)).e2 + q ^ 2) :=
  charpoly_factorization_of_maxwellResidual_add_rankOne S f x q
    (CharacteristicData.ofEndomorphism (S + rankOneEndomorphism f x))
    hq hS hdim htrace
    (hasCharacteristicData_ofEndomorphism
      (S + rankOneEndomorphism f x) hdim)

/-- The canonically extracted characteristic coefficients themselves have the
forced Rainich--Kaluza factorization form. -/
theorem characteristicData_ofEndomorphism_eq_from_maxwellResidual_add_rankOne
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0) :
    CharacteristicData.ofEndomorphism (S + rankOneEndomorphism f x) =
      CharacteristicData.fromFactorization
        { ricciTrace :=
            (CharacteristicData.ofEndomorphism
              (S + rankOneEndomorphism f x)).e1
          qSq := q ^ 2
          residualConstant :=
            -((CharacteristicData.ofEndomorphism
              (S + rankOneEndomorphism f x)).e2 + q ^ 2) } :=
  characteristicData_eq_from_maxwellResidual_add_rankOne S f x q
    (CharacteristicData.ofEndomorphism (S + rankOneEndomorphism f x))
    hq hS hdim htrace
    (hasCharacteristicData_ofEndomorphism
      (S + rankOneEndomorphism f x) hdim)

/-- The candidate polynomial obstruction is therefore a genuine necessary
condition of the complete four-dimensional square-law plus rank-one entrance
package. -/
theorem kaluzaObstruction_of_maxwellResidual_add_rankOne
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0) :
    kaluzaObstruction
      (CharacteristicData.ofEndomorphism
        (S + rankOneEndomorphism f x)) = 0 := by
  rw [characteristicData_ofEndomorphism_eq_from_maxwellResidual_add_rankOne
    S f x q hq hS hdim htrace]
  exact kaluzaObstruction_fromFactorization _

/-- On the nonzero Ricci-trace branch, the curvature coefficient formula now
recovers the actual protected magnitude `q^2` of the decomposed endomorphism. -/
theorem reconstructedQSq_of_maxwellResidual_add_rankOne
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ)
    (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hRicciTrace :
      (CharacteristicData.ofEndomorphism
        (S + rankOneEndomorphism f x)).e1 ≠ 0) :
    reconstructedQSq
      (CharacteristicData.ofEndomorphism
        (S + rankOneEndomorphism f x)) = q ^ 2 := by
  rw [characteristicData_ofEndomorphism_eq_from_maxwellResidual_add_rankOne
    S f x q hq hS hdim htrace]
  exact reconstructedQSq_fromFactorization _ hRicciTrace

end RainichKaluza
