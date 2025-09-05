import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- swap: Swap two elements in an array.
    
    Takes an array and two indices i and j, and swaps the elements
    at those positions. The array is modified in place.
    
    Requires: 0 ≤ i < arr.size and 0 ≤ j < arr.size
    
    Modifies the array so that:
    - arr[i] becomes the old value of arr[j]
    - arr[j] becomes the old value of arr[i]
    - All other elements remain unchanged
-/
def swap (arr : Array Int) (i : Nat) (j : Nat) : StateM (Array Int) Unit := sorry

/-- Specification: swap exchanges the elements at positions i and j.
    
    Precondition: 0 ≤ i < arr.size and 0 ≤ j < arr.size
    Postcondition: 
    - arr[i] = old(arr[j])
    - arr[j] = old(arr[i])
    - All other elements unchanged
-/
theorem swap_spec (arr : Array Int) (i j : Nat) 
    (hi : i < arr.size) (hj : j < arr.size) :
    ⦃⌜i < arr.size ∧ j < arr.size⌝⦄
    swap arr i j
    ⦃⇓_ => λ arr' => ⌜∃ (hi' : i < arr'.size) (hj' : j < arr'.size),
                      arr'[i]'hi' = arr[j]'hj ∧ 
                      arr'[j]'hj' = arr[i]'hi ∧
                      ∀ k (hk' : k < arr'.size) (hk : k < arr.size), 
                        k ≠ i ∧ k ≠ j → arr'[k]'hk' = arr[k]'hk⌝⦄ := by
  sorry
