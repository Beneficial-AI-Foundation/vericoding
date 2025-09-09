import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def poly2leg {n : Nat} (pol : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem poly2leg_spec {n : Nat} (pol : Vector Float n) :
    ⦃⌜True⌝⦄
    poly2leg pol
    ⦃⇓result => ⌜∀ i : Fin n, ∃ c : Float, result.get i = c⌝⦄ := by
  sorry
