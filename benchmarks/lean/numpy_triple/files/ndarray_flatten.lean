-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flatten {rows cols : Nat} (mat : Vector (Vector Float cols) rows) : Id (Vector Float (rows * cols)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flatten_spec {rows cols : Nat} (mat : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    flatten mat
    ⦃⇓result => ⌜result.size = rows * cols ∧ 
                 ∀ (r : Fin rows) (c : Fin cols), 
                 -- Elements are preserved in row-major order
                 True⌝⦄ := by
  sorry
-- </vc-theorems>