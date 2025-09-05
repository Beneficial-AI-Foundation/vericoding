import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- minArray: Find the minimum element in a non-empty array.
    
    Given a non-empty array of integers, returns the minimum value.
    
    Example: minArray([3, 1, 4, 1, 5]) = 1
-/
def minArray (a : Array Int) : Int := sorry

/-- Specification: minArray returns the minimum element in the array.
    
    Precondition: The array is non-empty
    Postcondition: 
    - The result is less than or equal to all elements
    - The result equals some element in the array
-/
theorem minArray_spec (a : Array Int) :
    ⦃⌜a.size > 0⌝⦄
    (pure (minArray a) : Id _)
    ⦃⇓r => ⌜
      (∀ i : Fin a.size, r ≤ a[i]) ∧
      (∃ i : Fin a.size, r = a[i])
    ⌝⦄ := by
  sorry
