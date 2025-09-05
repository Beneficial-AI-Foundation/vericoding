import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Compute the average of two integers.
    
    Computes the integer average (floor division) of two integers.
    
    Specification from Dafny:
    - result = (a + b) / 2 (integer division)
-/
def computeAvg (a : Int) (b : Int) : Int :=
  (a + b) / 2

/-- Specification: computeAvg returns the integer average.
    
    Precondition: True (no special preconditions)
    Postcondition: result = (a + b) / 2
-/
theorem computeAvg_spec (a : Int) (b : Int) :
    ⦃⌜True⌝⦄
    (pure (computeAvg a b) : Id _)
    ⦃⇓result => ⌜result = (a + b) / 2⌝⦄ := by
  sorry
