-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def eye {n : Nat} : Id (Vector (Vector Float n) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem eye_spec {n : Nat} :
    ⦃⌜True⌝⦄
    eye
    ⦃⇓result => ⌜
      -- Basic structure: diagonal ones, off-diagonal zeros
      (∀ i : Fin n, ∀ j : Fin n, 
        (result.get i).get j = if i = j then 1.0 else 0.0) ∧
      -- Symmetry property (identity matrices are symmetric)
      (∀ i : Fin n, ∀ j : Fin n, 
        (result.get i).get j = (result.get j).get i) ∧
      -- Uniqueness property: exactly one 1.0 in each row
      (∀ i : Fin n, ∃ j : Fin n, (result.get i).get j = 1.0 ∧ 
        ∀ k : Fin n, (result.get i).get k = 1.0 → k = j) ∧
      -- Uniqueness property: exactly one 1.0 in each column
      (∀ j : Fin n, ∃ i : Fin n, (result.get i).get j = 1.0 ∧ 
        ∀ k : Fin n, (result.get k).get j = 1.0 → k = i) ∧
      -- All non-diagonal elements are exactly 0.0
      (∀ i : Fin n, ∀ j : Fin n, i ≠ j → (result.get i).get j = 0.0)
    ⌝⦄ := by
  sorry
-- </vc-theorems>