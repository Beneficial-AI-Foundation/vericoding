-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_modf {n : Nat} (x : Vector Float n) : Id (Vector Float n × Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_modf_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_modf x
    ⦃⇓result => ⌜∀ i : Fin n, 
      let frac := result.1.get i
      let int := result.2.get i
      let orig := x.get i
      -- Parts sum to original
      (frac + int = orig) ∧
      -- Fractional part has absolute value less than 1
      (Float.abs frac < 1) ∧
      -- Both parts have same sign as original (or are zero)
      ((orig ≥ 0 → frac ≥ 0 ∧ int ≥ 0) ∧ (orig < 0 → frac ≤ 0 ∧ int ≤ 0)) ∧
      -- Integral part is truncated towards zero (floor for positive, ceiling for negative)
      (orig ≥ 0 → int = Float.floor orig) ∧
      (orig < 0 → int = -Float.floor (-orig))⌝⦄ := by
  sorry
-- </vc-theorems>