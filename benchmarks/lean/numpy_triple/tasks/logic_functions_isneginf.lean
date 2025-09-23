-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isneginf {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isneginf_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isneginf x
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Primary property: result is true iff input is negative infinity
      (result[i] = ((x[i]).isInf ∧ (x[i]) < 0)) ∧
      -- Sanity checks: finite values return false
      (¬(x[i]).isInf → result[i] = false) ∧
      -- Positive infinity returns false
      ((x[i]).isInf ∧ (x[i]) > 0 → result[i] = false) ∧
      -- NaN is not negative infinity
      ((x[i]).isNaN → result[i] = false) ∧
      -- Zero is not negative infinity
      (x[i] = 0.0 → result[i] = false) ∧
      -- Mathematical property: if result is true, then x is infinite and negative
      (result[i] = true → (x[i]).isInf ∧ (x[i]) < 0) ∧
      -- Exclusivity: cannot be both negative infinity and NaN
      (result[i] = true → ¬(x[i]).isNaN)⌝⦄ := by
  sorry
-- </vc-theorems>