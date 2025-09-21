-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_flatiter {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_flatiter_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_flatiter a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = a.get i⌝⦄ := by
  sorry
-- </vc-theorems>