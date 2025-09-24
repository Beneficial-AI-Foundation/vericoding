-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_hypot {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_hypot_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_hypot x1 x2
    ⦃⇓result => ⌜∀ i : Fin n,
      -- Core specification: Pythagorean theorem
      result.get i = Float.sqrt (x1.get i ^ 2 + x2.get i ^ 2) ∧
      -- Result is non-negative
      result.get i ≥ 0 ∧
      -- Result is at least as large as the absolute value of each input
      result.get i ≥ Float.abs (x1.get i) ∧
      result.get i ≥ Float.abs (x2.get i) ∧
      -- Special cases
      (x1.get i = 0 → result.get i = Float.abs (x2.get i)) ∧
      (x2.get i = 0 → result.get i = Float.abs (x1.get i))⌝⦄ := by
  sorry
-- </vc-theorems>