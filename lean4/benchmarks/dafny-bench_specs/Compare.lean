import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Compare: Generic equality comparison for any type with decidable equality.

    Returns true if the two inputs are equal, false otherwise.
-/
def compare {T : Type} [DecidableEq T] (a b : T) : Id Bool :=
  sorry

/-- Specification: Compare returns true iff the inputs are equal.

    Precondition: True (works for any inputs)
    Postcondition: 
      1. If a = b, then result = true
      2. If a ≠ b, then result = false
-/
theorem compare_spec {T : Type} [DecidableEq T] (a b : T) :
    ⦃⌜True⌝⦄
    compare a b
    ⦃⇓eq => ⌜(a = b → eq = true) ∧ (a ≠ b → eq = false)⌝⦄ := by
  sorry