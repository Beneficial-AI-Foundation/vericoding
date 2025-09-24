-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_floor_divide {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_floor_divide_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜∀ i : Fin n, x2.get i ≠ 0⌝⦄
    numpy_floor_divide x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, 
        result.get i = (x1.get i / x2.get i).floor ∧
        result.get i ≤ x1.get i / x2.get i ∧
        x1.get i / x2.get i < result.get i + 1⌝⦄ := by
  sorry
-- </vc-theorems>