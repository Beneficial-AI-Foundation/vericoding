import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def sum {n : Nat} (a : Vector Float n) : Id Float :=
  sorry

theorem sum_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    sum a
    ⦃⇓result => ⌜result = (a.toList.foldl (· + ·) 0) ∧ 
                 (n = 0 → result = 0) ∧
                 (∀ i : Fin n, a.get i = 0) → result = 0⌝⦄ := by
  sorry
