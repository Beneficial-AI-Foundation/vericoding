import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- CanyonSearch: Find the minimum absolute difference between elements of two sorted arrays.

    Given two non-empty sorted arrays, finds the minimum absolute difference
    between any element from the first array and any element from the second array.
-/
def canyonSearch (a : Array Int) (b : Array Int) : Nat := sorry

/-- Specification: CanyonSearch finds the minimum absolute difference between array elements.

    Precondition: 
      1. Both arrays are non-empty
      2. Both arrays are sorted in non-decreasing order
    Postcondition: 
      1. There exist indices i, j such that d equals |a[i] - b[j]|
      2. For all indices i, j, d ≤ |a[i] - b[j]|
-/
theorem canyonSearch_spec (a b : Array Int) 
    (ha_nonempty : a.size > 0) 
    (hb_nonempty : b.size > 0)
    (ha_sorted : ∀ i j : Fin a.size, i < j → a[i] ≤ a[j])
    (hb_sorted : ∀ i j : Fin b.size, i < j → b[i] ≤ b[j]) :
    ⦃⌜True⌝⦄
    (pure (canyonSearch a b) : Id _)
    ⦃⇓d => ⌜(∃ i : Fin a.size, ∃ j : Fin b.size, 
              d = Int.natAbs (a[i] - b[j])) ∧
            (∀ i : Fin a.size, ∀ j : Fin b.size, 
              d ≤ Int.natAbs (a[i] - b[j]))⌝⦄ := by
  sorry
