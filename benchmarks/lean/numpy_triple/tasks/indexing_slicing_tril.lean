-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tril {n : Nat} (matrix : Vector Float (n * n)) : Id (Vector Float (n * n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tril_spec {n : Nat} (matrix : Vector Float (n * n)) :
    ⦃⌜True⌝⦄
    tril matrix
    ⦃⇓result => ⌜
      -- The result has the same shape as the input
      result.size = matrix.size ∧
      -- For the lower triangle (i ≥ j), elements are preserved
      (∀ i : Fin n, ∀ j : Fin n, i.val ≥ j.val → 
        ∃ (hi : i.val * n + j.val < n * n) (hj : i.val * n + j.val < n * n),
          result.get ⟨i.val * n + j.val, hi⟩ = matrix.get ⟨i.val * n + j.val, hj⟩) ∧
      -- For the upper triangle (i < j), elements are zero
      (∀ i : Fin n, ∀ j : Fin n, i.val < j.val → 
        ∃ (hi : i.val * n + j.val < n * n),
          result.get ⟨i.val * n + j.val, hi⟩ = 0)⌝⦄ := by
  sorry
-- </vc-theorems>