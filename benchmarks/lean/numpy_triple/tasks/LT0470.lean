-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lagmul {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) : Id (Vector Float (n + m + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lagmul_spec {n m : Nat} (c1 : Vector Float (n + 1)) (c2 : Vector Float (m + 1)) :
    ⦃⌜True⌝⦄
    lagmul c1 c2
    ⦃⇓result => ⌜result.size = n + m + 1 ∧ 
                 ∀ i : Fin (n + m + 1), result.get i ≠ 0 → 
                   ∃ (j : Fin (n + 1)) (k : Fin (m + 1)), 
                     j.val + k.val = i.val ∧ c1.get j ≠ 0 ∧ c2.get k ≠ 0⌝⦄ := by
  sorry
-- </vc-theorems>