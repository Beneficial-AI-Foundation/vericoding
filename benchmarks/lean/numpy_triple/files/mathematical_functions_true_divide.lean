-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def true_divide {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem true_divide_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜∀ i : Fin n, x2.get i ≠ 0⌝⦄
    true_divide x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i / x2.get i ∧ 
                  result.get i = (x1.get i * (1 / x2.get i)) ∧
                  (x2.get i * result.get i = x1.get i)⌝⦄ := by
  sorry
-- </vc-theorems>