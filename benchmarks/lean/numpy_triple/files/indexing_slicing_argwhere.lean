import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def argwhere {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  sorry

theorem argwhere_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    argwhere a
    ⦃⇓indices => ⌜
      (∀ i ∈ indices, a.get i ≠ 0) ∧
      (∀ i : Fin n, a.get i ≠ 0 → i ∈ indices) ∧
      (indices.Nodup) ∧
      (∀ i j : Fin n, i ∈ indices → j ∈ indices → i < j → 
        indices.idxOf i < indices.idxOf j) ∧
      (indices = [] ↔ ∀ i : Fin n, a.get i = 0)
    ⌝⦄ := by
  sorry
