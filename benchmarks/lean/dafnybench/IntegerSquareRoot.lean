import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- squareRoot: Compute the integer square root of a natural number.

    Returns the largest natural number r such that r² ≤ N.
    This is the floor of the real square root of N.

    For example:
    - squareRoot 4 = 2
    - squareRoot 5 = 2
    - squareRoot 8 = 2
    - squareRoot 9 = 3
-/
def squareRoot (N : Nat) : Nat := sorry

/-- Specification: squareRoot returns the integer square root of N.

    Precondition: True (works for any natural number)
    Postcondition: r² ≤ N < (r+1)²

    This ensures that r is the largest natural number whose square doesn't exceed N.
-/
theorem squareRoot_spec (N : Nat) :
    ⦃⌜True⌝⦄
    (pure (squareRoot N) : Id _)
    ⦃⇓r => ⌜r * r ≤ N ∧ N < (r + 1) * (r + 1)⌝⦄ := by
  sorry
