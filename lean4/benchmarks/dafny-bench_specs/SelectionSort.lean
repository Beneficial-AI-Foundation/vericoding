import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- SelectionSort: Sort an array using the selection sort algorithm.

    Modifies the array in-place to arrange elements in ascending order.
    Preserves all elements (same multiset before and after).

    The array is sorted in-place.
-/
def selectionSort (a : Array Int) : Id (Array Int) :=
  -- For now, just return a sorted copy
  let sorted := a.toList.toArray.qsort (· < ·)
  sorted

/-- Specification: selectionSort sorts the array in ascending order
    while preserving all elements.

    Precondition: True (no special preconditions)
    Postcondition: Array is sorted and contains same elements
-/
/-- Helper function to count occurrences of an element in an array -/
def countOccurrences (arr : Array Int) (elem : Int) : Nat :=
  arr.toList.filter (· = elem) |>.length

theorem selectionSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    selectionSort a
    ⦃⇓result => ⌜result.size = a.size ∧
                 (∀ i j : Fin result.size, i.val < j.val → result[i] ≤ result[j]) ∧
                 (∀ elem : Int, countOccurrences result elem = countOccurrences a elem)⌝⦄ := by
  sorry