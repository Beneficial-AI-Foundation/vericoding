-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reduce {n : Nat} (op : Float → Float → Float) (arr : Vector Float (n + 1)) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reduce_spec {n : Nat} (op : Float → Float → Float) (arr : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    reduce op arr
    ⦃⇓result => ⌜(n = 0 → result = arr.get ⟨0, Nat.zero_lt_succ _⟩) ∧
                 (n > 0 → ∃ (fold_fn : Fin (n + 1) → Float), 
                          fold_fn ⟨0, Nat.zero_lt_succ _⟩ = arr.get ⟨0, Nat.zero_lt_succ _⟩ ∧
                          (∀ i : Fin n, fold_fn ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = 
                            op (fold_fn ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) 
                               (arr.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) ∧
                          result = fold_fn ⟨n, Nat.lt_succ_self _⟩)⌝⦄ := by
  sorry
-- </vc-theorems>