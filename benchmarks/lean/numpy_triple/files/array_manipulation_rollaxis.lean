import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_rollaxis {n : Nat} (a : Vector Float n) (axis : Int) (start : Int := 0) : Id (Vector Float n) :=
  sorry

theorem numpy_rollaxis_spec {n : Nat} (a : Vector Float n) (axis : Int) (start : Int := 0) :
    ⦃⌜True⌝⦄
    numpy_rollaxis a axis start
    ⦃⇓result => ⌜result = a⌝⦄ := by
  sorry
