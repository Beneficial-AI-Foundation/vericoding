-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def place {n k v : Nat} (arr : Vector Float n) (mask : Vector Bool n) (vals : Vector Float (v + 1))
    (h : k = (mask.toArray.toList.count true)) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem place_spec {n k v : Nat} (arr : Vector Float n) (mask : Vector Bool n) (vals : Vector Float (v + 1))
    (h : k = (mask.toArray.toList.count true)) :
    ⦃⌜k = (mask.toArray.toList.count true)⌝⦄
    place arr mask vals h
    ⦃⇓result => 
      -- Elements where mask is False remain unchanged, 
      -- Elements where mask is True are replaced with values from vals (with repetition)
      ⌜(∀ i : Fin n, mask.get i = false → result.get i = arr.get i) ∧
       (∀ i : Fin n, mask.get i = true → 
         ∃ (pos : Nat) (val_idx : Fin (v + 1)), 
           pos < k ∧ 
           val_idx.val = pos % (v + 1) ∧
           result.get i = vals.get val_idx)⌝
    ⦄ := by
  sorry
-- </vc-theorems>