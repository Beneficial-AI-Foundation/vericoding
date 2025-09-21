-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_searchsorted {n m : Nat} (a : Vector Float n) (v : Vector Float m) : Id (Vector (Fin (n + 1)) m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>