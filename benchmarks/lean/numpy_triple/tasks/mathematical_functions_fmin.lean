-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fmin {n : Nat} (x y : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fmin_spec {n : Nat} (x y : Vector Float n) :
    ⦃⌜True⌝⦄
    fmin x y
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- NaN handling cases
      (¬(x.get i).isNaN ∧ ¬(y.get i).isNaN → 
        result.get i = min (x.get i) (y.get i)) ∧
      ((x.get i).isNaN ∧ ¬(y.get i).isNaN → 
        result.get i = y.get i) ∧
      (¬(x.get i).isNaN ∧ (y.get i).isNaN → 
        result.get i = x.get i) ∧
      ((x.get i).isNaN ∧ (y.get i).isNaN → 
        (result.get i).isNaN) ∧
      -- Mathematical properties
      (¬(x.get i).isNaN ∧ ¬(y.get i).isNaN → 
        result.get i ≤ x.get i ∧ result.get i ≤ y.get i) ∧
      (¬(result.get i).isNaN → 
        (result.get i = x.get i ∨ result.get i = y.get i))⌝⦄ := by
  sorry
-- </vc-theorems>