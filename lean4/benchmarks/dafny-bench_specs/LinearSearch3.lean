import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- linearSearch3: Search for an element satisfying a predicate in an array.

    This is a generic version of linear search that finds the first element
    satisfying a given predicate P. The precondition guarantees that at least
    one such element exists.
    
    This is more flexible than searching for a specific value, as it can
    search based on any property.
-/
def linearSearch3 {T : Type} (a : Array T) (P : T → Bool) : Id Nat :=
  match a.findIdx? P with
  | some idx => pure idx
  | none => panic! "No element satisfying predicate (violates precondition)"

/-- Specification: linearSearch3 returns the index of the first element satisfying predicate P.

    Precondition: There exists an index i such that P(a[i]) is true
    Postcondition:
    - P(a[n]) is true for the returned index n
    - For all indices k < n, P(a[k]) is false
-/
theorem linearSearch3_spec {T : Type} [Inhabited T] (a : Array T) (P : T → Bool) :
    ⦃⌜∃ i : Fin a.size, P (a[i]) = true⌝⦄
    linearSearch3 a P
    ⦃⇓n => ⌜n < a.size ∧ P (a[n]!) = true ∧ (∀ k : Nat, k < n → P (a[k]!) = false)⌝⦄ := by
  sorry