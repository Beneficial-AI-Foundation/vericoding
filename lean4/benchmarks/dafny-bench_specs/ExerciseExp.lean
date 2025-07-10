import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Exponential Function

This module ports the Dafny specification for an exponential function `exp(x, e)`
that computes `x^e` for non-negative exponents.

The specification includes:
- A recursive definition of exponentiation
- A lemma that `exp(3, n) - 1` is even for all `n ≥ 1`
- A lemma that `exp(3, 2*n) - 1` is divisible by 8 for all `n ≥ 1`
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseExp

/-- Exponential function computing x^e for non-negative e -/
def exp (x : Int) (e : Nat) : Int := sorry

/-- Specification: exp preserves positivity -/
theorem exp_positive (x : Int) (e : Nat) (h : x > 0) : exp x e > 0 := by
  sorry

/-- Lemma: For n ≥ 1, (3^n - 1) is even -/
theorem exp3_lemma (n : Nat) (h : n ≥ 1) : (exp 3 n - 1) % 2 = 0 := by
  sorry

/-- Lemma: For n ≥ 1, (3^(2n) - 1) is divisible by 8 -/
theorem mult8_lemma (n : Nat) (h : n ≥ 1) : (exp 3 (2 * n) - 1) % 8 = 0 := by
  sorry

/-- Hoare triple for exp function -/
theorem exp_spec (x : Int) (e : Nat) :
    ⦃⌜e ≥ 0⌝⦄ 
    (pure (exp x e) : Id Int)
    ⦃⇓result => ⌜x > 0 → result > 0⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseExp