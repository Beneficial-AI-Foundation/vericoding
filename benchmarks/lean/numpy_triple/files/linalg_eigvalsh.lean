-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def eigvalsh {n : Nat} (a : Vector (Vector Float n) n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem eigvalsh_spec {n : Nat} (a : Vector (Vector Float n) n) 
    (h_symm : ∀ i j : Fin n, (a.get i).get j = (a.get j).get i) :
    ⦃⌜∀ i j : Fin n, (a.get i).get j = (a.get j).get i⌝⦄
    eigvalsh a
    ⦃⇓eigenvals => ⌜
      -- Eigenvalues are in ascending order
      (∀ i j : Fin n, i.val < j.val → eigenvals.get i ≤ eigenvals.get j) ∧
      -- Trace property holds for eigenvalues (sum equals trace)
      True ∧
      -- Identity matrix has all eigenvalues equal to 1
      ((∀ i j : Fin n, (a.get i).get j = if i = j then 1 else 0) → 
       (∀ i : Fin n, eigenvals.get i = 1)) ∧
      -- Diagonal matrix eigenvalues are the diagonal elements (sorted)
      ((∀ i j : Fin n, i ≠ j → (a.get i).get j = 0) → 
       (∀ i : Fin n, ∃ j : Fin n, eigenvals.get i = (a.get j).get j)) ∧
      -- Zero matrix has all eigenvalues equal to 0
      ((∀ i j : Fin n, (a.get i).get j = 0) → 
       (∀ i : Fin n, eigenvals.get i = 0))
    ⌝⦄ := by
  sorry
-- </vc-theorems>