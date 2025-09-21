-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_diff {n : Nat} (a : Vector Float (n + 1)) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_diff_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_diff a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = a.get ⟨i.val + 1, by simp [Fin.is_lt]⟩ - a.get ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩⌝⦄ := by
  sorry
-- </vc-theorems>