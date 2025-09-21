-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isposinf {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isposinf_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isposinf x
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Primary property: result is true iff input is positive infinity
      (result.get i = ((x.get i).isInf ∧ (x.get i) > 0)) ∧
      -- Sanity checks: finite values return false
      (¬(x.get i).isInf → result.get i = false) ∧
      -- Negative infinity returns false
      ((x.get i).isInf ∧ (x.get i) < 0 → result.get i = false) ∧
      -- NaN is not positive infinity
      ((x.get i).isNaN → result.get i = false) ∧
      -- Zero is not positive infinity
      (x.get i = 0.0 → result.get i = false) ∧
      -- Mathematical property: if result is true, then x is infinite and positive
      (result.get i = true → (x.get i).isInf ∧ (x.get i) > 0) ∧
      -- Exclusivity: cannot be both positive infinity and NaN
      (result.get i = true → ¬(x.get i).isNaN)⌝⦄ := by
  sorry
-- </vc-theorems>