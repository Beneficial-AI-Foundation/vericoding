import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- linearSearch: Search for an element in an array using linear search.

    Scans the array from left to right looking for the element e.
    Returns the index of the first occurrence of e, or the array length if e is not found.
    
    This variant returns array.size when the element is not found, making it
    easy to check if the search was successful by comparing with array.size.
-/
def linearSearch (a : Array Int) (e : Int) : Id Nat :=
  match a.findIdx? (· = e) with
  | some idx => pure idx
  | none => pure a.size

/-- Specification: linearSearch returns the index of the first occurrence of e,
    or a.size if e is not in the array.

    Precondition: True (no special preconditions)
    Postcondition:
    - 0 ≤ n ≤ a.size
    - If n = a.size, then e is not in the array
    - If n < a.size, then a[n] = e
    - All elements before index n are not equal to e
-/
theorem linearSearch_spec (a : Array Int) (e : Int) :
    ⦃⌜True⌝⦄
    linearSearch a e
    ⦃⇓n => ⌜0 ≤ n ∧ n ≤ a.size ∧
            (n = a.size ∨ (n < a.size ∧ a[n]! = e)) ∧
            (∀ i : Nat, i < n → a[i]! ≠ e)⌝⦄ := by
  sorry