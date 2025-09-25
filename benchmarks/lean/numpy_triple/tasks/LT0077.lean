-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_transpose {rows cols : Nat} (a : Vector (Vector Float cols) rows) : 
    Id (Vector (Vector Float rows) cols) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_transpose_spec {rows cols : Nat} (a : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    numpy_transpose a
    ⦃⇓result => ⌜∀ (i : Fin rows) (j : Fin cols), 
                  (result.get j).get i = (a.get i).get j⌝⦄ := by
  sorry
-- </vc-theorems>