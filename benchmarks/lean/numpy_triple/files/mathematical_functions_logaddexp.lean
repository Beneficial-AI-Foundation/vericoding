-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def logaddexp {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem logaddexp_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    logaddexp x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log (Float.exp (x1.get i) + Float.exp (x2.get i)) ∧
                   result.get i ≥ max (x1.get i) (x2.get i) ∧
                   (x1.get i = x2.get i → result.get i = x1.get i + Float.log 2)⌝⦄ := by
  sorry
-- </vc-theorems>