import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Sum: Calculate the sum of integers from 0 to N.

    Computes the sum 0 + 1 + 2 + ... + N using the formula N * (N + 1) / 2.
-/
def sum (N : Nat) : Id Int :=
  sorry

/-- Specification: Sum returns the sum of integers from 0 to N.

    Precondition: N ≥ 0 (enforced by Nat type)
    Postcondition: result = N * (N + 1) / 2
-/
theorem sum_spec (N : Nat) :
    ⦃⌜True⌝⦄
    sum N
    ⦃⇓result => ⌜result = N * (N + 1) / 2⌝⦄ := by
  sorry