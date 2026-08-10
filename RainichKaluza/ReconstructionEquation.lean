import RainichKaluza.LorentzianScalarBlock
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel

/-!
# Coordinate-free reconstruction equation

This file derives the Sylvester-type equation used by the eigenbasis analysis.
The proof is valid in any associative real algebra, so matrices and linear
endomorphisms are special cases. The geometric work still has to establish the
premises from the convention-fixed EMD equations.
-/

namespace RainichKaluza

/-- **Exact noncommutative algebra theorem.** If `R = S + V`, the Maxwell part
squares to a scalar multiple of the identity, and the rank-one scalar part
squares to its trace times itself, then `V` satisfies the reconstruction
equation used throughout the project. -/
theorem reconstructionEquation_of_decomposition
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S V : A) (traceV qSq : ℝ)
    (hS : S * S = qSq • (1 : A))
    (hV : V * V = traceV • V) :
    let R := S + V
    R * V + V * R - traceV • V = R * R - qSq • (1 : A) := by
  dsimp
  calc
    (S + V) * V + V * (S + V) - traceV • V =
        S * V + V * S + V * V := by
      simp only [add_mul, mul_add, hV]
      abel
    _ = (S + V) * (S + V) - qSq • (1 : A) := by
      simp only [add_mul, mul_add, hS, hV]
      abel

/-- The same identity with the Ricci-like element supplied explicitly. -/
theorem reconstructionEquation_of_eq_add
    {A : Type*} [Ring A] [Algebra ℝ A]
    (R S V : A) (traceV qSq : ℝ)
    (hR : R = S + V)
    (hS : S * S = qSq • (1 : A))
    (hV : V * V = traceV • V) :
    R * V + V * R - traceV • V = R * R - qSq • (1 : A) := by
  subst R
  exact reconstructionEquation_of_decomposition S V traceV qSq hS hV

end RainichKaluza
