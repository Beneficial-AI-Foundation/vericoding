import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def prod {n : Nat} (a : Vector Float n) : Id Float :=
  sorry

theorem prod_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    prod a
    ⦃⇓result => ⌜result = (a.toList.foldl (· * ·) 1) ∧ 
                 (n = 0 → result = 1) ∧
                 (∃ i : Fin n, a.get i = 0) → result = 0⌝⦄ := by
  sorry
