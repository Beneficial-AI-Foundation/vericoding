import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- onlineMax: Find the position of the first element after index x that is greater 
    than the maximum of elements before x.
    
    Given an array and an index x, finds the maximum element in the range [0, x),
    then returns the index of the first element in [x, array.length) that exceeds
    this maximum. If no such element exists, returns array.length - 1.
    
    Example: onlineMax([3, 1, 4, 1, 5], 2) returns (m=3, p=2) since max of [3,1] is 3
             and element at index 2 (which is 4) is the first that exceeds 3.
-/
def onlineMax (a : Array Int) (x : Nat) : Id (Int × Nat) :=
  -- Find max in [0, x)
  let rec findMaxBefore (i : Nat) (currentMax : Int) : Int :=
    if h : i < x then
      if h2 : i < a.size then
        let elem := a[i]
        if elem > currentMax then
          findMaxBefore (i + 1) elem
        else
          findMaxBefore (i + 1) currentMax
      else
        currentMax
    else
      currentMax
  
  let m := if h : 0 < a.size then findMaxBefore 1 a[0] else 0
  
  -- Find first position >= x where element > m
  let rec findFirstGreater (i : Nat) : Nat :=
    if h : i < a.size then
      if a[i] > m then
        i
      else
        findFirstGreater (i + 1)
    else
      a.size - 1
  
  (m, findFirstGreater x)

/-- Specification: onlineMax finds the maximum in [0,x) and the position of the
    first element that exceeds it.
    
    Precondition: 
    - 1 ≤ x < a.size
    - a.size ≠ 0
    
    Postcondition:
    - x ≤ p < a.size
    - m is the maximum of elements in [0,x)
    - m equals some element in [0,x)
    - If p < a.size - 1, then all elements in [0,p) are < a[p]
    - If all elements in [x, a.size) are ≤ m, then p = a.size - 1
-/
theorem onlineMax_spec (a : Array Int) (x : Nat) :
    ⦃⌜1 ≤ x ∧ x < a.size ∧ a.size ≠ 0⌝⦄
    onlineMax a x
    ⦃⇓(m, p) => ⌜
      x ≤ p ∧ p < a.size ∧
      (∀ i : Nat, i < x → a[i]'(by sorry) ≤ m) ∧
      (∃ i : Nat, i < x ∧ a[i]'(by sorry) = m) ∧
      (p < a.size - 1 → (∀ i : Nat, i < p → a[i]'(by sorry) < a[p]'(by sorry))) ∧
      ((∀ i : Nat, x ≤ i ∧ i < a.size → a[i]'(by sorry) ≤ m) → p = a.size - 1)
    ⌝⦄ := by
  sorry