import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- SwapArithmeticReconstructed: Swap two integer values (reconstructed version).
    
    Takes two integers X and Y and returns them swapped,
    so that the first output is Y and the second output is X.
    This is a reconstructed version of the swap arithmetic specification.
    
    Returns a pair with the values swapped.
-/
def swapArithmeticReconstructed (X : Int) (Y : Int) : (Int × Int) :=
  (Y, X)

/-- Specification: swapArithmeticReconstructed returns the input values swapped.
    
    Precondition: True (no special preconditions)
    Postcondition: First output is Y, second output is X
-/
theorem swapArithmeticReconstructed_spec (X : Int) (Y : Int) :
    ⦃⌜True⌝⦄
    (pure (swapArithmeticReconstructed X Y) : Id _)
    ⦃⇓result => ⌜let (x, y) := result
                 x = Y ∧ y = X⌝⦄ := by
  sorry
