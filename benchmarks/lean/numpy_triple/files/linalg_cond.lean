-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def conditionNumber {n : Nat} (x : Vector (Vector Float n) n) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem conditionNumber_spec {n : Nat} (x : Vector (Vector Float n) n) 
    (h_nonempty : n > 0) :
    ⦃⌜n > 0⌝⦄
    conditionNumber x
    ⦃⇓result => ⌜result ≥ 0 ∧ result ≥ 1⌝⦄ := by
  sorry
-- </vc-theorems>