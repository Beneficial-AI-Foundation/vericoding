-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def atleast_2d {n : Nat} (arr : Vector Float n) : Id (Vector (Vector Float n) 1) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem atleast_2d_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    atleast_2d arr
    ⦃⇓result => ⌜-- Shape property: result has exactly 1 row
                  result.size = 1 ∧
                  -- Row content property: the single row matches the input
                  ∃ row : Vector Float n, 
                  result = Vector.singleton row ∧ 
                  -- Element preservation: all elements are preserved in order
                  ∀ i : Fin n, row.get i = arr.get i ∧
                  -- Mathematical property: this is equivalent to creating a 1×n matrix
                  -- where the input vector forms the single row
                  result.get ⟨0, by simp⟩ = row⌝⦄ := by
  sorry
-- </vc-theorems>