-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def column_stack {rows cols : Nat} (arrays : Vector (Vector Float rows) cols) : 
    Id (Vector Float (rows * cols)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem column_stack_spec {rows cols : Nat} (arrays : Vector (Vector Float rows) cols) 
    (h_cols : cols > 0) :
    ⦃⌜cols > 0⌝⦄
    column_stack arrays
    ⦃⇓result => ⌜∀ (i : Fin rows) (j : Fin cols), 
                  result.get ⟨j.val * rows + i.val, sorry⟩ = (arrays.get j).get i⌝⦄ := by
  sorry
-- </vc-theorems>