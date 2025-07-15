import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.searchsorted: Find indices where elements should be inserted to maintain order.

    Given a sorted array `a` and values `v`, returns indices such that inserting 
    each element of `v` at the corresponding index would preserve the sorted order of `a`.
    
    This implementation focuses on the 'left' side behavior where for each value v[i],
    it returns the leftmost suitable insertion position. The returned indices are
    in the range [0, n] where n is the length of the sorted array.
-/
def numpy_searchsorted {n m : Nat} (a : Vector Float n) (v : Vector Float m) : Id (Vector (Fin (n + 1)) m) :=
  sorry

/-- Specification: numpy.searchsorted returns indices for sorted insertion.

    Precondition: The input array `a` must be sorted in ascending order
    Postcondition: For each element v[i], the returned index idx satisfies:
    - All elements before idx are strictly less than v[i] (left insertion property)
    - All elements at or after idx are greater than or equal to v[i] (sorted property)
    - The index is valid for insertion (between 0 and n inclusive)
    - Inserting v[i] at idx preserves the sorted order of the array
-/
theorem numpy_searchsorted_spec {n m : Nat} (a : Vector Float n) (v : Vector Float m) 
    (h_sorted : ∀ i j : Fin n, i < j → a.get i ≤ a.get j) :
    ⦃⌜∀ i j : Fin n, i < j → a.get i ≤ a.get j⌝⦄
    numpy_searchsorted a v
    ⦃⇓indices => ⌜∀ k : Fin m, 
        let idx := indices.get k
        -- Left insertion property: all elements before idx are strictly less than v[k]
        (∀ i : Fin n, i.val < idx.val → a.get i < v.get k) ∧
        -- Sorted property: all elements at or after idx are greater than or equal to v[k]
        (∀ j : Fin n, idx.val ≤ j.val → v.get k ≤ a.get j) ∧
        -- Leftmost property: idx is the leftmost valid insertion point
        (∀ pos : Fin (n + 1), pos.val < idx.val → 
            ∃ i : Fin n, i.val < pos.val ∧ a.get i ≥ v.get k)⌝⦄ := by
  sorry