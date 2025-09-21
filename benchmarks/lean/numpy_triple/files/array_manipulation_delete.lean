-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def delete {n : Nat} (arr : Vector Float (n + 1)) (index : Fin (n + 1)) : 
    Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem delete_spec {n : Nat} (arr : Vector Float (n + 1)) (index : Fin (n + 1)) :
    ⦃⌜True⌝⦄
    delete arr index
    ⦃⇓result => ⌜(∀ i : Fin n, 
                   if h : i.val < index.val then 
                     result.get i = arr.get ⟨i.val, by sorry⟩
                   else 
                     result.get i = arr.get ⟨i.val + 1, by sorry⟩) ∧
                 (∀ i : Fin (n + 1), i ≠ index → 
                   ∃ j : Fin n, result.get j = arr.get i)⌝⦄ := by
  sorry
-- </vc-theorems>