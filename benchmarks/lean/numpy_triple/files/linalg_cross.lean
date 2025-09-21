-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_linalg_cross (x1 x2 : Vector Float 3) : Id (Vector Float 3) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_linalg_cross_spec (x1 x2 : Vector Float 3) :
    ⦃⌜True⌝⦄
    numpy_linalg_cross x1 x2
    ⦃⇓result => ⌜result.get 0 = x1.get 1 * x2.get 2 - x1.get 2 * x2.get 1 ∧
                result.get 1 = x1.get 2 * x2.get 0 - x1.get 0 * x2.get 2 ∧
                result.get 2 = x1.get 0 * x2.get 1 - x1.get 1 * x2.get 0⌝⦄ := by
  sorry
-- </vc-theorems>