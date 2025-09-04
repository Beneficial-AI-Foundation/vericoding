import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Predicate to check if an array is sorted in non-decreasing order.
    
    This version explicitly states that every element is less than or equal
    to all later elements, which is stronger than just checking adjacent pairs
    but equivalent in meaning. -/
def isSorted (a : Array Int) : Prop :=
  ∀ i j : Nat, i < j ∧ j < a.size → a[i]! ≤ a[j]!

/-- Binary search implementation.
    
    Searches for a key K in a sorted array and returns whether it exists.
    
    Preconditions:
    - The array is sorted in non-decreasing order
    
    Postconditions:
    - Returns true iff there exists an index i such that a[i] = K
-/
def binSearch (a : Array Int) (K : Int) : Id Bool := do
  sorry -- Implementation left as exercise

theorem binSearch_spec (a : Array Int) (K : Int)
    (h_sorted : isSorted a) :
    ⦃⌜True⌝⦄
    binSearch a K
    ⦃⇓result => ⌜result = true ↔ ∃ i : Nat, i < a.size ∧ a[i]! = K⌝⦄ := by
  mvcgen [binSearch]
  sorry

/-- Alternative (weaker but equivalent) definition of sorted array.
    
    This version only checks adjacent elements. While equivalent to the
    stronger version, it requires additional lemmas to prove loop invariants
    in binary search, as noted in the original Dafny comments. -/
def isSorted_weak (a : Array Int) : Prop :=
  ∀ i : Nat, i < a.size - 1 → a[i]! ≤ a[i+1]!

/-- Lemma showing the two definitions of sorted are equivalent -/
theorem isSorted_equiv (a : Array Int) :
    isSorted a ↔ isSorted_weak a := by
  sorry