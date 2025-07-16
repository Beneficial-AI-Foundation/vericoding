import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Min: Find the minimum of two integers.
    
    Given two integers, returns the smaller one.
    
    Example: Min(5, 3) = 3
-/
def minOfTwo (x y : Int) : Id Int :=
  if x ≤ y then x else y

/-- Specification: minOfTwo returns the smaller of the two inputs.
    
    Precondition: True (no special preconditions)
    Postcondition: 
    - If x ≤ y, then result = x
    - If x > y, then result = y
-/
theorem minOfTwo_spec (x y : Int) :
    ⦃⌜True⌝⦄
    minOfTwo x y
    ⦃⇓z => ⌜
      (x ≤ y → z = x) ∧
      (x > y → z = y)
    ⌝⦄ := by
  sorry