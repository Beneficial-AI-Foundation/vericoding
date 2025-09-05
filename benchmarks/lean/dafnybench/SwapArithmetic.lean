import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- SwapArithmetic: Swap two integer values.

    Takes two integers X and Y and returns them swapped,
    so that the first output is Y and the second output is X.

    Returns a pair with the values swapped.
-/
def swapArithmetic (X : Int) (Y : Int) : Int × Int :=
  (Y, X)

/-- Specification: swapArithmetic returns the input values swapped.

    Precondition: True (no special preconditions)
    Postcondition: First output is Y, second output is X
-/
theorem swapArithmetic_spec (X : Int) (Y : Int) :
    ⦃⌜True⌝⦄
    (pure (swapArithmetic X Y) : Id _)
    ⦃⇓result => ⌜let (x, y) := result
                 x = Y ∧ y = X⌝⦄ := by
  sorry
