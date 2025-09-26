-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flatnonzero {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flatnonzero_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    flatnonzero a
    ⦃⇓result => ⌜
      -- All indices in result point to non-zero elements
      (∀ i ∈ result, a.get i ≠ 0) ∧
      -- All non-zero elements have their indices in result
      (∀ j : Fin n, a.get j ≠ 0 → j ∈ result) ∧
      -- Result contains no duplicate indices
      (result.Nodup) ∧
      -- Result indices are sorted in ascending order
      (∀ i j : Fin n, i ∈ result → j ∈ result → i < j → 
        result.idxOf i < result.idxOf j)
    ⌝⦄ := by
  sorry
-- </vc-theorems>