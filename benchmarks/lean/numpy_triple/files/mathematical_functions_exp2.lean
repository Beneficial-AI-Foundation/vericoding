import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def exp2 {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem exp2_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    exp2 x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (2 : Float) ^ (x.get i) ∧ 
                               result.get i > 0⌝⦄ := by
  sorry
