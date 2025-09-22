-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_diagonal {m n : Nat} (x : Vector (Vector Float n) m) (offset : Int) : Id (Vector Float (min m n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_diagonal_spec {m n : Nat} (x : Vector (Vector Float n) m) (offset : Int) 
    (h_m : m > 0) (h_n : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    numpy_diagonal x offset
    ⦃⇓result => ⌜
      -- Main diagonal case: result[i] = x[i][i] for all valid i
      (offset = 0 → ∀ i : Fin (min m n), 
        result.get i = (x.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left m n)⟩).get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right m n)⟩) ∧
      -- General case: diagonal elements are extracted according to offset
      -- The function produces a valid diagonal extraction for any offset value
      (∀ i : Fin (min m n), ∃ r c : Nat, 
        r < m ∧ c < n ∧ 
        result.get i = (x.get ⟨r, sorry⟩).get ⟨c, sorry⟩)
    ⌝⦄ := by
  sorry
-- </vc-theorems>