-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_insert {n : Nat} (arr : Vector α n) (idx : Fin (n + 1)) (value : α) : Id (Vector α (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_insert_spec {n : Nat} (arr : Vector α n) (idx : Fin (n + 1)) (value : α) :
    ⦃⌜True⌝⦄
    numpy_insert arr idx value
    ⦃⇓result => ⌜-- Elements before insertion point are preserved
                 (∀ i : Fin (n + 1), i < idx → 
                   ∃ (h : i.val < n), result.get i = arr.get ⟨i.val, h⟩) ∧ 
                 -- The new value is at the specified index
                 (result.get idx = value) ∧
                 -- Elements after insertion point are shifted
                 (∀ i : Fin (n + 1), idx < i → 
                   ∃ (h : i.val - 1 < n), result.get i = arr.get ⟨i.val - 1, h⟩) ∧
                 -- Sanity check: the result contains all original elements plus the new value
                 (∀ j : Fin n, ∃ i : Fin (n + 1), 
                   (i < idx ∧ i.val = j.val ∧ result.get i = arr.get j) ∨ 
                   (idx < i ∧ i.val = j.val + 1 ∧ result.get i = arr.get j))⌝⦄ := by
  sorry
-- </vc-theorems>