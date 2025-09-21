-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reduceat {n m : Nat} (op : Float → Float → Float) (arr : Vector Float n) 
    (indices : Vector (Fin n) m) : Id (Vector Float m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reduceat_spec {n m : Nat} (op : Float → Float → Float) (arr : Vector Float n) 
    (indices : Vector (Fin n) m) (h_arr_nonempty : n > 0) (h_indices_nonempty : m > 0) :
    ⦃⌜n > 0 ∧ m > 0⌝⦄
    reduceat op arr indices
    ⦃⇓result => ⌜
      -- Result has same length as indices
      result.toList.length = m ∧
      -- For each index position, the result is computed according to reduceat rules
      (∀ i : Fin m, 
        -- For non-last indices: handle slice [indices[i], indices[i+1])
        (i.val < m - 1 → 
          let start_idx := indices.get i
          let end_idx := indices.get ⟨i.val + 1, sorry⟩
          -- Case 1: Normal forward slice (start < end)
          (start_idx.val < end_idx.val → 
            ∃ (slice_elements : List Float),
            -- Extract elements from start to end-1
            slice_elements = (List.range (end_idx.val - start_idx.val)).map 
              (fun offset => arr.get ⟨start_idx.val + offset, sorry⟩) ∧
            slice_elements.length > 0 ∧
            -- Apply left-associative reduction
            result.get i = slice_elements.foldl op slice_elements.head!) ∧
          -- Case 2: Backward or equal indices (start >= end)
          (start_idx.val ≥ end_idx.val → 
            result.get i = arr.get start_idx)) ∧
        -- For the last index: reduce from indices[i] to end of array
        (i.val = m - 1 → 
          let start_idx := indices.get i
          let slice_elements := (List.range (n - start_idx.val)).map 
            (fun offset => arr.get ⟨start_idx.val + offset, sorry⟩)
          slice_elements.length > 0 ∧
          result.get i = slice_elements.foldl op slice_elements.head!)) ∧
      -- Mathematical properties of the reduction operation
      (∀ slice : List Float, slice.length > 0 → 
        -- Single element case
        (slice.length = 1 → slice.foldl op slice.head! = slice.head!) ∧
        -- Multiple element case follows left-associative folding
        (slice.length > 1 → 
          slice.foldl op slice.head! = 
          match slice with
          | [] => 0  -- Never reached due to length > 0
          | [a] => a
          | a :: rest => rest.foldl op a)) ∧
      -- Boundary conditions
      (∀ i : Fin m, 
        -- All indices are within bounds
        (indices.get i).val < n ∧
        -- Result elements are well-defined
        ∃ (reduction_result : Float), result.get i = reduction_result)
    ⌝⦄ := by
  sorry
-- </vc-theorems>