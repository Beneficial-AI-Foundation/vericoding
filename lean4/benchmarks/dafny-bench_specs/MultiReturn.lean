import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- MultipleReturns: Compute sum and difference of two integers.
    
    Given two integers x and y, returns both their sum (x+y) and difference (x-y).
    
    Example: MultipleReturns(5, 3) = (8, 2)
-/
def multipleReturns (x y : Int) : Id (Int × Int) :=
  (x + y, x - y)

/-- Specification: multipleReturns computes the sum and difference correctly.
    
    Precondition: True (no special preconditions)
    Postcondition: 
    - First component equals x + y
    - Second component equals x - y
-/
theorem multipleReturns_spec (x y : Int) :
    ⦃⌜True⌝⦄
    multipleReturns x y
    ⦃⇓(more, less) => ⌜more = x + y ∧ less = x - y⌝⦄ := by
  sorry