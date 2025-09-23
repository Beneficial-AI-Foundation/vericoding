-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legweight_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    legweight x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1.0⌝⦄ := by
  sorry
-- </vc-theorems>