-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vsplit {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (h_div : k > 0 ∧ rows % k = 0) : Id (Vector (Vector (Vector Float cols) (rows / k)) k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vsplit_spec {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (h_div : k > 0 ∧ rows % k = 0) :
    ⦃⌜k > 0 ∧ rows % k = 0⌝⦄
    vsplit mat h_div
    ⦃⇓result => ⌜-- Sanity check: correct size
                 (∀ split_idx : Fin k, (result.get split_idx).size = rows / k) ∧
                 -- Mathematical property: each split contains consecutive rows
                 (∀ split_idx : Fin k, ∀ row_idx : Fin (rows / k), ∀ col_idx : Fin cols,
                   -- The element at position (row_idx, col_idx) in split split_idx
                   -- equals the element at position (split_idx * (rows/k) + row_idx, col_idx) in the original matrix
                   ∃ (global_row : Fin rows), 
                     global_row.val = split_idx.val * (rows / k) + row_idx.val ∧
                     ((result.get split_idx).get row_idx).get col_idx = 
                     (mat.get global_row).get col_idx) ∧
                 -- Additional property: the splits partition the original matrix
                 (∀ orig_row : Fin rows, ∃ split_idx : Fin k, ∃ row_idx : Fin (rows / k),
                   orig_row.val = split_idx.val * (rows / k) + row_idx.val)⌝⦄ := by
  sorry
-- </vc-theorems>