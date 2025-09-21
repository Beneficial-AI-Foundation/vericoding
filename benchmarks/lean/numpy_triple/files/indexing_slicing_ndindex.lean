-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ndindex {m n : Nat} (shape : Nat × Nat) : Id (Vector (Fin m × Fin n) (m * n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ndindex_spec {m n : Nat} (shape : Nat × Nat) (h_shape : shape = (m, n)) :
    ⦃⌜shape = (m, n)⌝⦄
    ndindex shape
    ⦃⇓indices => ⌜indices.size = m * n ∧
                   (∀ k : Fin (m * n), 
                      let (i, j) := indices.get k
                      i.val < m ∧ j.val < n) ∧
                   (∀ i : Fin m, ∀ j : Fin n,
                      ∃ k : Fin (m * n), indices.get k = (i, j)) ∧
                   (∀ k : Fin (m * n), 
                      let (i, j) := indices.get k
                      k.val = i.val * n + j.val)⌝⦄ := by
  sorry
-- </vc-theorems>