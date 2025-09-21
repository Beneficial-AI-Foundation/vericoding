-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_bitwise_not {n : Nat} (x : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_bitwise_not_spec {n : Nat} (x : Vector Int n) :
    ⦃⌜True⌝⦄
    numpy_bitwise_not x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = -(x.get i + 1)⌝⦄ := by
  sorry
-- </vc-theorems>