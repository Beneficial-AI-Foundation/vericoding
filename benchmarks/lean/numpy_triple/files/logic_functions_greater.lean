-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_greater {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_greater_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_greater x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, (result.get i = true ↔ x1.get i > x2.get i) ∧
                             -- Antisymmetry: if x1 > x2 then not (x2 > x1)
                             (result.get i = true → ¬(x2.get i > x1.get i)) ∧
                             -- IEEE 754 compliance: NaN comparisons always return false
                             ((x1.get i).isNaN ∨ (x2.get i).isNaN → result.get i = false) ∧
                             -- Boolean result: each element is either true or false
                             (result.get i = true ∨ result.get i = false)⌝⦄ := by
  sorry
-- </vc-theorems>