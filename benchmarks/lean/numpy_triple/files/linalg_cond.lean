import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def conditionNumber {n : Nat} (x : Vector (Vector Float n) n) : Id Float :=
  sorry

theorem conditionNumber_spec {n : Nat} (x : Vector (Vector Float n) n) 
    (h_nonempty : n > 0) :
    ⦃⌜n > 0⌝⦄
    conditionNumber x
    ⦃⇓result => ⌜result ≥ 0 ∧ result ≥ 1⌝⦄ := by
  sorry
