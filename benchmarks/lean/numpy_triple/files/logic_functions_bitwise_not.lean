import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_bitwise_not {n : Nat} (x : Vector Int n) : Id (Vector Int n) :=
  sorry

theorem numpy_bitwise_not_spec {n : Nat} (x : Vector Int n) :
    ⦃⌜True⌝⦄
    numpy_bitwise_not x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = -(x.get i + 1)⌝⦄ := by
  sorry
