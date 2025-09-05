import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- ReturnSeven: A simple function that always returns 7.

    Takes any integer as input and returns the constant value 7.
    This is a trivial function useful for testing specifications.

    Returns: Always returns 7.
-/
def returnSeven (x : Int) : Int :=
  7

/-- Specification: returnSeven always returns the value 7,
    regardless of the input.

    Precondition: True (no special preconditions)
    Postcondition: The result is always 7
-/
theorem returnSeven_spec (x : Int) :
    ⦃⌜True⌝⦄
    (pure (returnSeven x) : Id _)
    ⦃⇓result => ⌜result = 7⌝⦄ := by
  sorry
