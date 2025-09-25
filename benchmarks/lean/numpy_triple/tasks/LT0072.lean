-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split {n k : Nat} (arr : Vector Float n) (h_div : k ∣ n) (h_pos : k > 0) : 
    Id (Vector (Vector Float (n / k)) k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_spec {n k : Nat} (arr : Vector Float n) (h_div : k ∣ n) (h_pos : k > 0) :
    ⦃⌜k ∣ n ∧ k > 0⌝⦄
    split arr h_div h_pos
    ⦃⇓result => ⌜(∀ i : Fin k, ∀ j : Fin (n / k), 
                  ∃ (idx : Fin n), idx.val = i.val * (n / k) + j.val ∧ 
                  (result.get i).get j = arr.get idx) ∧
                 (∀ idx : Fin n, ∃ (i : Fin k) (j : Fin (n / k)), 
                  idx.val = i.val * (n / k) + j.val ∧
                  arr.get idx = (result.get i).get j)⌝⦄ := by
  sorry
-- </vc-theorems>