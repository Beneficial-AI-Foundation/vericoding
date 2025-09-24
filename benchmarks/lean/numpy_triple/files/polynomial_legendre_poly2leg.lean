-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def poly2leg {n : Nat} (pol : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem poly2leg_spec {n : Nat} (pol : Vector Float n) :
    ⦃⌜True⌝⦄
    poly2leg pol
    ⦃⇓result => ⌜∀ i : Fin n, ∃ c : Float, result.get i = c⌝⦄ := by
  sorry
-- </vc-theorems>