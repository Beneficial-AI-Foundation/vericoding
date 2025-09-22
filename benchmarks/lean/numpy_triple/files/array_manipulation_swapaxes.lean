-- <vc-preamble>
import Init.Data.Vector.Basic
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swapaxes {rows cols : Nat} (mat : Vector (Vector Float cols) rows) 
    (axis1 axis2 : Nat) (h1 : axis1 < 2) (h2 : axis2 < 2) : 
    Id (Vector (Vector Float rows) cols) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swapaxes_spec {rows cols : Nat} (mat : Vector (Vector Float cols) rows) 
    (h1 : rows > 0) (h2 : cols > 0) :
    ⦃⌜rows > 0 ∧ cols > 0⌝⦄
    swapaxes mat 0 1 (by decide) (by decide)
    ⦃⇓result => ⌜∀ (i : Fin rows) (j : Fin cols), 
                  (mat.get i).get j = (result.get j).get i⌝⦄ := by
  sorry
-- </vc-theorems>