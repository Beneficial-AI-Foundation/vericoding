import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_negative {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem numpy_negative_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_negative x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = -(x.get i)⌝⦄ := by
  sorry
