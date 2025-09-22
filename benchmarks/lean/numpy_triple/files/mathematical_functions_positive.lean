-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def positive {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positive_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    positive x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = x.get i) ∧
                 (∀ i : Fin n, Float.abs (result.get i) = Float.abs (x.get i))⌝⦄ := by
  sorry
-- </vc-theorems>