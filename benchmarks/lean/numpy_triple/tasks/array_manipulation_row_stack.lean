-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def row_stack {n m : Nat} (arrays : Vector (Vector Float n) m) : Id (Vector (Vector Float n) m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem row_stack_spec {n m : Nat} (arrays : Vector (Vector Float n) m) :
    ⦃⌜True⌝⦄
    row_stack arrays
    ⦃⇓result => ⌜∀ i : Fin m, ∀ j : Fin n, (result.get i).get j = (arrays.get i).get j⌝⦄ := by
  sorry
-- </vc-theorems>