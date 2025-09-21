-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fmax {n : Nat} (x y : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fmax_spec {n : Nat} (x y : Vector Float n) :
    ⦃⌜True⌝⦄
    fmax x y
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Core NaN handling behavior
      (¬(x.get i).isNaN ∧ ¬(y.get i).isNaN → 
        result.get i = max (x.get i) (y.get i)) ∧
      ((x.get i).isNaN ∧ ¬(y.get i).isNaN → 
        result.get i = y.get i) ∧
      (¬(x.get i).isNaN ∧ (y.get i).isNaN → 
        result.get i = x.get i) ∧
      ((x.get i).isNaN ∧ (y.get i).isNaN → 
        (result.get i).isNaN) ∧
      -- Mathematical properties for non-NaN cases
      (¬(x.get i).isNaN ∧ ¬(y.get i).isNaN → 
        result.get i ≥ x.get i ∧ result.get i ≥ y.get i) ∧
      (¬(x.get i).isNaN ∧ ¬(y.get i).isNaN → 
        (result.get i = x.get i ∨ result.get i = y.get i)) ∧
      -- NaN preservation: result is NaN iff both inputs are NaN
      ((result.get i).isNaN ↔ ((x.get i).isNaN ∧ (y.get i).isNaN))⌝⦄ := by
  sorry
-- </vc-theorems>