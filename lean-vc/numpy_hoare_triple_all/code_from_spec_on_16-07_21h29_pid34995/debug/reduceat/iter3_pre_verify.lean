import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "ufunc.reduceat",
  "category": "Reduction Method",
  "description": "Performs a (local) reduce with specified slices over a single axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ufunc.reduceat.html",
  "signature": "ufunc.reduceat(array, indices, axis=0, dtype=None, out=None)",
  "parameters": {
    "array": "Input array",
    "indices": "Indices specifying slice boundaries",
    "axis": "Axis along which to apply reduceat",
    "dtype": "Data type for intermediate computations",
    "out": "Location for the result"
  },
  "notes": [
    "Applies reduction to specified slices of the array",
    "Useful for segmented reductions"
  ]
}
-/

/-- 
Universal function reduceat method: Performs reductions on specified slices of an array.

For each index pair (indices[i], indices[i+1]), applies the reduction operation 
to the slice array[indices[i]:indices[i+1]].

Special behavior:
- For the last index, reduces from indices[i] to the end of the array
- If indices[i] >= indices[i+1], uses only the element at indices[i]
- Output length equals the number of indices provided

Example: np.add.reduceat([1,2,3,4,5,6,7,8], [0,4,1,5]) applies addition to slices:
- [1,2,3,4] -> 10
- [2,3,4,5] -> 14  
- [5,6,7,8] -> 26
Result: [10, 14, 26]
-/
def reduceat {n m : Nat} (op : Float → Float → Float) (arr : Vector Float n) 
    (indices : Vector (Fin n) m) : Id (Vector Float m) :=
  pure <| Vector.ofFn fun i : Fin m =>
    let start_idx := indices.get i
    if i.val < m - 1 then
      let end_idx := indices.get ⟨i.val + 1, by {
        have h1 : i.val < m := i.isLt
        have h2 : i.val < m - 1 := by assumption
        omega
      }⟩
      if start_idx.val < end_idx.val then
        let slice_elements := (List.range (end_idx.val - start_idx.val)).map 
          (fun offset => arr.get ⟨start_idx.val + offset, by {
            have h1 : start_idx.val < n := start_idx.isLt
            have h2 : offset < end_idx.val - start_idx.val := by {
              rw [List.mem_range] at *
              assumption
            }
            omega
          }⟩)
        match slice_elements with
        | [] => 0
        | head :: tail => tail.foldl op head
      else
        arr.get start_idx
    else
      let slice_elements := (List.range (n - start_idx.val)).map 
        (fun offset => arr.get ⟨start_idx.val + offset, by {
          have h1 : start_idx.val < n := start_idx.isLt
          have h2 : offset < n - start_idx.val := by {
            rw [List.mem_range] at *
            assumption
          }
          omega
        }⟩)
      match slice_elements with
      | [] => 0
      | head :: tail => tail.foldl op head

-- LLM HELPER
lemma fin_succ_lt {m : Nat} {i : Fin m} (h : i.val < m - 1) : i.val + 1 < m := by
  cases m with
  | zero => simp at i
  | succ k => 
    simp at h
    exact Nat.succ_lt_succ h

-- LLM HELPER
lemma slice_nonempty {n start_idx end_idx : Nat} (h1 : start_idx < n) (h2 : start_idx < end_idx) (h3 : end_idx ≤ n) : 
  (List.range (end_idx - start_idx)).length > 0 := by
  simp [List.length_range]
  exact Nat.sub_pos_of_lt h2

-- LLM HELPER
lemma last_slice_nonempty {n start_idx : Nat} (h1 : start_idx < n) : 
  (List.range (n - start_idx)).length > 0 := by
  simp [List.length_range]
  exact Nat.sub_pos_of_lt h1

-- LLM HELPER  
lemma list_head_foldl_eq {α : Type*} (op : α → α → α) (a : α) (l : List α) :
  (a :: l).foldl op a = l.foldl op a := by
  simp [List.foldl]

/-- 
Specification: reduceat applies a binary operation to reduce specified slices of an array.

This captures the core behavior of NumPy's ufunc.reduceat method:
1. For each index i in the indices vector, compute a slice of the input array
2. Apply the binary operation to reduce that slice to a single value
3. Return a vector of these reduced values

Precondition: Both input array and indices must be non-empty
Postcondition: 
- Result has same length as indices vector
- For each index position i:
  - If i < m-1: reduce slice from indices[i] to indices[i+1] (exclusive)
  - If i = m-1: reduce slice from indices[i] to end of array
  - If indices[i] >= indices[i+1]: use single element at indices[i]
- Each slice reduction follows left-associative folding
- Empty slices are handled by returning the identity or single element

Mathematical Properties:
- Segmented reduction: each output element corresponds to a specific segment
- Associativity: the reduction operation is applied left-associatively
- Boundary handling: last index always reduces to end of array
- Non-increasing indices: handled by single element selection
-/
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
          let end_idx := indices.get ⟨i.val + 1, fin_succ_lt (by assumption)⟩
          -- Case 1: Normal forward slice (start < end)
          (start_idx.val < end_idx.val → 
            ∃ (slice_elements : List Float),
            -- Extract elements from start to end-1
            slice_elements = (List.range (end_idx.val - start_idx.val)).map 
              (fun offset => arr.get ⟨start_idx.val + offset, by {
                have h1 : start_idx.val < n := start_idx.isLt
                have h2 : offset < end_idx.val - start_idx.val := by {
                  rw [List.mem_range] at *
                  assumption
                }
                omega
              }⟩) ∧
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
            (fun offset => arr.get ⟨start_idx.val + offset, by {
              have h1 : start_idx.val < n := start_idx.isLt
              have h2 : offset < n - start_idx.val := by {
                rw [List.mem_range] at *
                assumption
              }
              omega
            }⟩)
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
  apply Std.Do.triple_intro
  · exact ⟨h_arr_nonempty, h_indices_nonempty⟩
  · intro result
    rw [reduceat, pure_bind, Id.pure_eq, Id.bind_eq]
    constructor
    · simp [Vector.toList_length, Vector.length_ofFn]
    constructor
    · intro i h_not_last
      constructor
      · intro h_forward
        simp [Vector.get_ofFn]
        use (List.range (indices.get ⟨i.val + 1, fin_succ_lt h_not_last⟩).val - (indices.get i).val)).map 
          (fun offset => arr.get ⟨(indices.get i).val + offset, by {
            have h1 : (indices.get i).val < n := (indices.get i).isLt
            have h2 : offset < indices.get ⟨i.val + 1, fin_succ_lt h_not_last⟩.val - (indices.get i).val := by {
              rw [List.mem_range] at *
              assumption
            }
            omega
          }⟩)
        constructor
        · rfl
        constructor
        · apply slice_nonempty
          · exact (indices.get i).isLt
          · exact h_forward
          · simp
        · simp [Vector.get_ofFn]
          split_ifs with h1 h2
          · rw [List.length_range] at h2
            exact h_forward
          · simp at h1
            exact absurd h_not_last h1
      · intro h_backward
        simp [Vector.get_ofFn]
        split_ifs with h1 h2
        · rw [List.length_range] at h2
          exact absurd h_backward h2
        · simp at h1
          exact absurd h_not_last h1
    · intro i h_last
      simp [Vector.get_ofFn]
      constructor
      · apply last_slice_nonempty
        exact (indices.get i).isLt
      · split_ifs with h1
        · simp at h1
          exact absurd h_last h1
        · simp at h1
          rfl
    constructor
    · intro slice h_nonempty
      constructor
      · intro h_single
        cases slice with
        | nil => simp at h_nonempty
        | cons head tail =>
          simp at h_single
          simp [h_single, List.foldl]
      · intro h_multi
        cases slice with
        | nil => simp at h_nonempty
        | cons head tail =>
          simp [List.foldl]
    · intro i
      constructor
      · exact (indices.get i).isLt
      · use (reduceat op arr indices).run.get i
        rfl