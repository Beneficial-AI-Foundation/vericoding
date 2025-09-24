-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_argwhere {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_argwhere_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_argwhere a
    ⦃⇓indices => ⌜
      (∀ i ∈ indices, a.get i ≠ 0) ∧
      (∀ i : Fin n, a.get i ≠ 0 → i ∈ indices) ∧
      (indices.Nodup) ∧
      (∀ i j : Fin n, i ∈ indices → j ∈ indices → i < j → 
        indices.idxOf i < indices.idxOf j)
    ⌝⦄ := by
  sorry
-- </vc-theorems>