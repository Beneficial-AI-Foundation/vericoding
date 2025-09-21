-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_logaddexp2 {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_logaddexp2_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_logaddexp2 x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log2 (Float.exp2 (x1.get i) + Float.exp2 (x2.get i)) ∧
                  result.get i ≥ max (x1.get i) (x2.get i) ∧
                  result.get i ≤ max (x1.get i) (x2.get i) + 1⌝⦄ := by
  sorry
-- </vc-theorems>