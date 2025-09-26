-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def matrix_rank {m n : Nat} (A : Vector (Vector Float n) m) : Id Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matrix_rank_spec {m n : Nat} (A : Vector (Vector Float n) m) :
    ⦃⌜True⌝⦄
    matrix_rank A
    ⦃⇓result => ⌜
      -- Basic bounds: rank is bounded by matrix dimensions
      result ≤ min m n ∧
      -- Zero matrix has rank 0
      ((∀ i : Fin m, ∀ j : Fin n, (A.get i).get j = 0) → result = 0) ∧
      -- Identity matrix has full rank (for square matrices)
      ((m = n) → 
        (∀ i : Fin m, ∀ j : Fin n, (A.get i).get j = if i.val = j.val then 1 else 0) → 
        result = n) ∧
      -- If any row is all zeros, rank is less than m
      ((∃ i : Fin m, ∀ j : Fin n, (A.get i).get j = 0) → result < m) ∧
      -- If any column is all zeros, rank is less than n  
      ((∃ j : Fin n, ∀ i : Fin m, (A.get i).get j = 0) → result < n) ∧
      -- If two rows are identical, rank is less than m (when m > 1)
      ((m > 1) → 
        (∃ i₁ i₂ : Fin m, i₁ ≠ i₂ ∧ (∀ j : Fin n, (A.get i₁).get j = (A.get i₂).get j)) → 
        result < m) ∧
      -- If two columns are identical, rank is less than n (when n > 1)
      ((n > 1) → 
        (∃ j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ (∀ i : Fin m, (A.get i).get j₁ = (A.get i).get j₂)) → 
        result < n) ∧
      -- For 1×1 matrices, rank is 1 if non-zero, 0 if zero
      ((m = 1 ∧ n = 1) → 
        ∃ h₁ : 0 < m, ∃ h₂ : 0 < n,
        (result = 1 ↔ (A.get ⟨0, h₁⟩).get ⟨0, h₂⟩ ≠ 0))
    ⌝⦄ := by
  sorry
-- </vc-theorems>