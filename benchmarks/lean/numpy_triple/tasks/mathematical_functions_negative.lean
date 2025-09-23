-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_negative {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_negative_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_negative x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = -(x.get i)⌝⦄ := by
  sorry
-- </vc-theorems>