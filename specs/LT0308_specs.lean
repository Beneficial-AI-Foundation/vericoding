-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_exp {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_exp_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_exp x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.exp (x.get i) ∧ 
                   result.get i > 0 ∧
                   (x.get i = 0 → result.get i = 1) ∧
                   (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j)⌝⦄ := by
  sorry
-- </vc-theorems>