-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def float_power {n : Nat} (base : Vector Float n) (exponent : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem float_power_spec {n : Nat} (base : Vector Float n) (exponent : Vector Float n) 
    (h_valid : ∀ i : Fin n, (base.get i > 0) ∨ (base.get i = 0 ∧ exponent.get i ≥ 0)) :
    ⦃⌜∀ i : Fin n, (base.get i > 0) ∨ (base.get i = 0 ∧ exponent.get i ≥ 0)⌝⦄
    float_power base exponent
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (base.get i) ^ (exponent.get i)⌝⦄ := by
  sorry
-- </vc-theorems>