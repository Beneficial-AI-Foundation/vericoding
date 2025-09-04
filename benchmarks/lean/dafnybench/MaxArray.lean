import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- maxArray: Find the maximum element in a non-empty array.
    
    Given a non-empty array of integers, returns the maximum value.
    
    Example: maxArray([3, 1, 4, 1, 5]) = 5
-/
def maxArray (a : Array Int) : Id Int :=
  let rec findMax (i : Nat) (currentMax : Int) : Int :=
    if h : i < a.size then
      let elem := a[i]
      if elem > currentMax then
        findMax (i + 1) elem
      else
        findMax (i + 1) currentMax
    else
      currentMax
  if h : 0 < a.size then
    findMax 1 a[0]
  else
    0 -- This case should not happen given precondition

/-- Specification: maxArray returns the maximum element in the array.
    
    Precondition: The array is non-empty
    Postcondition: 
    - The result is greater than or equal to all elements
    - The result equals some element in the array
-/
theorem maxArray_spec (a : Array Int) :
    ⦃⌜a.size ≥ 1⌝⦄
    maxArray a
    ⦃⇓m => ⌜
      (∀ k : Fin a.size, m ≥ a[k]) ∧
      (∃ k : Fin a.size, m = a[k])
    ⌝⦄ := by
  sorry