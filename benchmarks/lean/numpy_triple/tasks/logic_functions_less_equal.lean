-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def less_equal {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem less_equal_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    less_equal x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (x1.get i ≤ x2.get i) ∧
                 (result.get i = true ↔ x1.get i ≤ x2.get i) ∧
                 (result.get i = false ↔ x1.get i > x2.get i) ∧
                 (x1.get i = x2.get i → result.get i = true)⌝⦄ := by
  sorry
-- </vc-theorems>