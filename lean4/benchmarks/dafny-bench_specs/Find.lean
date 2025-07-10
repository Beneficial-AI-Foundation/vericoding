import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Find: Search for a key in an array and return its index.

    Searches for the first occurrence of a key in an array and returns its index.
    Returns -1 if the key is not found in the array.

    This implements a linear search algorithm.
-/
def find (a : Array Int) (key : Int) : Id Int :=
  match a.findIdx? (· = key) with
  | some idx => pure (idx : Int)
  | none => pure (-1)

/-- Specification: find returns the index of the first occurrence of key in array a,
    or -1 if key is not found.

    Precondition: True (no special preconditions)
    Postcondition:
    - The returned index is between -1 and a.size - 1 (inclusive)
    - If index ≠ -1, then a[index] = key and all earlier elements are not equal to key
    - If index = -1, then no element in the array equals key
-/
theorem find_spec (a : Array Int) (key : Int) :
    ⦃⌜True⌝⦄
    find a key
    ⦃⇓index => ⌜-1 ≤ index ∧ index < a.size ∧
                (index ≠ -1 → a[index.toNat]! = key ∧ 
                  (∀ i : Nat, i < index.toNat → a[i]! ≠ key)) ∧
                (index = -1 → ∀ i : Fin a.size, a[i] ≠ key)⌝⦄ := by
  mvcgen [find]
  sorry