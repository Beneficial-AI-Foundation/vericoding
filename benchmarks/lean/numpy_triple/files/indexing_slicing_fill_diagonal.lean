-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fill_diagonal {T : Type} {rows cols : Nat} (mat : Vector (Vector T cols) rows) (val : T) : 
    Id (Vector (Vector T cols) rows) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fill_diagonal_spec {T : Type} {rows cols : Nat} (mat : Vector (Vector T cols) rows) (val : T) :
    ⦃⌜True⌝⦄
    fill_diagonal mat val
    ⦃⇓result => ⌜-- Diagonal elements are filled with val
      (∀ i : Fin rows, ∀ j : Fin cols, i.val = j.val → 
        (result.get i).get j = val) ∧
      -- Non-diagonal elements remain unchanged
      (∀ i : Fin rows, ∀ j : Fin cols, i.val ≠ j.val → 
        (result.get i).get j = (mat.get i).get j)⌝⦄ := by
  sorry
-- </vc-theorems>