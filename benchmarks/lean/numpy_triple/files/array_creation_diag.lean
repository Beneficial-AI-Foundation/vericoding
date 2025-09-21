-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diag {n : Nat} (v : Vector Float n) : Id (Vector (Vector Float n) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diag_spec {n : Nat} (v : Vector Float n) :
    ⦃⌜True⌝⦄
    diag v
    ⦃⇓result => ⌜
      -- 1. Elements on the main diagonal are from v
      (∀ i : Fin n, (result.get i).get i = v.get i) ∧

      -- 2. All off-diagonal elements are zero
      (∀ i j : Fin n, i ≠ j → (result.get i).get j = 0) ∧

      -- 3. Sanity check: diagonal matrix property - non-zero elements only on diagonal
      (∀ i j : Fin n, (result.get i).get j ≠ 0 → i = j) ∧

      -- 4. Matrix trace equals sum of input vector elements
      (List.sum (List.map (fun i => (result.get i).get i) (List.finRange n)) = 
       List.sum (List.map (fun i => v.get i) (List.finRange n))) ∧

      -- 5. The resulting matrix is symmetric
      (∀ i j : Fin n, (result.get i).get j = (result.get j).get i) ∧

      -- 6. Row and column sums: for each row/column, sum equals the corresponding diagonal element
      (∀ i : Fin n, 
        List.sum (List.map (fun j => (result.get i).get j) (List.finRange n)) = v.get i) ∧
      (∀ j : Fin n,
        List.sum (List.map (fun i => (result.get i).get j) (List.finRange n)) = v.get j) ∧

      -- 7. Determinant property: det(diag(v)) = product of diagonal elements
      -- (This is a fundamental property of diagonal matrices, though we don't compute it here)

      -- 8. Each row has exactly one non-zero element at position i (unless v[i] = 0)
      (∀ i : Fin n, v.get i ≠ 0 → 
        ((result.get i).get i ≠ 0 ∧ ∀ j : Fin n, j ≠ i → (result.get i).get j = 0)) ∧

      -- 9. Each column has exactly one non-zero element at position j (unless v[j] = 0)
      (∀ j : Fin n, v.get j ≠ 0 → 
        ((result.get j).get j ≠ 0 ∧ ∀ i : Fin n, i ≠ j → (result.get i).get j = 0))
    ⌝⦄ := by
  sorry
-- </vc-theorems>