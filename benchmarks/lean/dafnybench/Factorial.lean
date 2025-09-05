import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Factorial

This module implements a specification for computing factorials.
It includes both the recursive mathematical definition and an iterative implementation specification.
-/

namespace DafnyBenchmarks

/-- Recursive definition of factorial -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Iterative implementation of factorial -/
def iterativeFactorial (n : Nat) : Nat := sorry

/-- Specification for iterativeFactorial -/
theorem iterativeFactorial_spec (n : Nat) :
  ⦃⌜True⌝⦄
  (pure (iterativeFactorial n) : Id _)
  ⦃⇓result => ⌜result = factorial n⌝⦄ := by
  sorry

end DafnyBenchmarks
