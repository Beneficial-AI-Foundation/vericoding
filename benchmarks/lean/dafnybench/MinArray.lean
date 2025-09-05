import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- minArray: Find the minimum element in a non-empty array.
    
    Given a non-empty array of integers, returns the minimum value.
    
    Example: minArray([3, 1, 4, 1, 5]) = 1
-/
def minArray (a : Array Int) : Int :=
  let rec findMin (i : Nat) (currentMin : Int) : Int :=
    if h : i < a.size then
      let elem := a[i]
      if elem < currentMin then
        findMin (i + 1) elem
      else
        findMin (i + 1) currentMin
    else
      currentMin
  if h : 0 < a.size then
    findMin 1 a[0]
  else
    0 -- This case should not happen given precondition

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
