-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_power {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_power_spec {n : Nat} (x1 x2 : Vector Float n) 
    (h_valid : ∀ i : Fin n, (x1.get i = 0 → x2.get i ≥ 0) ∧ 
                            (x1.get i < 0 → (x2.get i).floor = x2.get i)) :
    ⦃⌜∀ i : Fin n, (x1.get i = 0 → x2.get i ≥ 0) ∧ 
                    (x1.get i < 0 → (x2.get i).floor = x2.get i)⌝⦄
    numpy_power x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i ^ x2.get i ∧
                               (x2.get i = 0 ∧ x1.get i ≠ 0 → result.get i = 1) ∧
                               (x2.get i = 1 → result.get i = x1.get i) ∧
                               (x1.get i > 1 ∧ x2.get i > 0 → result.get i > x1.get i)⌝⦄ := by
  sorry
-- </vc-theorems>