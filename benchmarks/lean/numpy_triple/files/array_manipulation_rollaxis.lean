-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_rollaxis {n : Nat} (a : Vector Float n) (axis : Int) (start : Int := 0) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_rollaxis_spec {n : Nat} (a : Vector Float n) (axis : Int) (start : Int := 0) :
    ⦃⌜True⌝⦄
    numpy_rollaxis a axis start
    ⦃⇓result => ⌜result = a⌝⦄ := by
  sorry
-- </vc-theorems>