import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def positive {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem positive_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    positive x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = x.get i) ∧
                 (∀ i : Fin n, Float.abs (result.get i) = Float.abs (x.get i))⌝⦄ := by
  sorry
