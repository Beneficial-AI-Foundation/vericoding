-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    add x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i + x2.get i⌝⦄ := by
  sorry
-- </vc-theorems>