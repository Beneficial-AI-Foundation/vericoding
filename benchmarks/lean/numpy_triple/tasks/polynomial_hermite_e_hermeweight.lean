-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermeweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermeweight_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    hermeweight x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.exp (-(x.get i)^2 / 2) ∧
                  result.get i > 0 ∧
                  (∀ j : Fin n, result.get i = result.get j ↔ Float.abs (x.get i) = Float.abs (x.get j))⌝⦄ := by
  sorry
-- </vc-theorems>