import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def lagmulx {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float (n + 2)) :=
  sorry

theorem lagmulx_spec {n : Nat} (c : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    lagmulx c
    ⦃⇓result => ⌜result.size = n + 2 ∧ 
                 result.get 0 = c.get 0 ∧
                 result.get 1 = -c.get 0⌝⦄ := by
  sorry
