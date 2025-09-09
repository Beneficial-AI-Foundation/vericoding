import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def average {n : Nat} (a : Vector Float (n + 1)) (weights : Option (Vector Float (n + 1))) : Id Float :=
  sorry

theorem average_spec {n : Nat} (a : Vector Float (n + 1)) (weights : Option (Vector Float (n + 1))) :
    ⦃⌜True⌝⦄
    average a weights
    ⦃⇓result => ⌜(weights.isNone → 
        ∃ sum_a : Float, result = sum_a / Float.ofNat (n + 1)) ∧
      (∀ w, weights = some w → 
        ∃ sum_aw sum_w : Float, result = sum_aw / sum_w ∧ sum_w ≠ 0)⌝⦄ := by
  sorry
