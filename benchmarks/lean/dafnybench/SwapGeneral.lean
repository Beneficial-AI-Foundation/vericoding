import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Swap: General swap function for two integer values.
    
    Takes two integers X and Y and returns them swapped,
    so that the first output is Y and the second output is X.
    This is the general swap specification.
    
    Returns a pair with the values swapped.
-/
def swapGeneral (X : Int) (Y : Int) : Int × Int := sorry

/-- Specification: swapGeneral returns the input values swapped.
    
    Precondition: True (no special preconditions)
    Postcondition: First output is Y, second output is X
-/
theorem swapGeneral_spec (X : Int) (Y : Int) :
    ⦃⌜True⌝⦄
    (pure (swapGeneral X Y) : Id _)
    ⦃⇓result => ⌜let (x, y) := result
                 x = Y ∧ y = X⌝⦄ := by
  sorry
