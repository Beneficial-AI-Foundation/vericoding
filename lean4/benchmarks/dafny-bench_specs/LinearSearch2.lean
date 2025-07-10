import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- linearSearch2: Search for an element that is guaranteed to exist in the array.

    This variant of linear search has a precondition that the element exists
    in the array, so it always returns a valid index.
    
    This is useful when you know the element is present and want to avoid
    handling the "not found" case.
-/
def linearSearch2 (a : Array Int) (e : Int) : Id Nat :=
  match a.findIdx? (· = e) with
  | some idx => pure idx
  | none => panic! "Element not found (violates precondition)"

/-- Specification: linearSearch2 returns the index of the first occurrence of e.

    Precondition: There exists an index i such that a[i] = e
    Postcondition:
    - The returned index n satisfies a[n] = e
    - All elements before index n are not equal to e
-/
theorem linearSearch2_spec (a : Array Int) (e : Int) :
    ⦃⌜∃ i : Fin a.size, a[i] = e⌝⦄
    linearSearch2 a e
    ⦃⇓n => ⌜n < a.size ∧ a[n]! = e ∧ (∀ k : Nat, k < n → a[k]! ≠ e)⌝⦄ := by
  mvcgen [linearSearch2]
  sorry