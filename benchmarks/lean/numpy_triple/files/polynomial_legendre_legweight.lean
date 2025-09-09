import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def legweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem legweight_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    legweight x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1.0⌝⦄ := by
  sorry
