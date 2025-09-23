-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ravel {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ravel_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    ravel a
    ⦃⇓result => ⌜result = a⌝⦄ := by
  sorry
-- </vc-theorems>