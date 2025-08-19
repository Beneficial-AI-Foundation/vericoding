import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.diagonal",
  "category": "Diagonal operations",
  "description": "Return specified diagonals",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diagonal.html",
  "doc": "Return specified diagonals.\n\nIf \`a\` is 2-D, returns the diagonal of \`a\` with the given offset, i.e., the collection of elements of the form \`\`a[i, i+offset]\`\`. If \`a\` has more than two dimensions, then the axes specified by \`axis1\` and \`axis2\` are used to determine the 2-D sub-array whose diagonal is returned. The shape of the resulting array can be determined by removing \`axis1\` and \`axis2\` and appending an index to the right equal to the size of the resulting diagonals.\n\nParameters\n----------\na : array_like\n    Array from which the diagonals are taken.\noffset : int, optional\n    Offset of the diagonal from the main diagonal. Can be positive or negative.\naxis1 : int, optional\n    Axis to be used as the first axis of the 2-D sub-arrays from which the diagonals should be taken.\naxis2 : int, optional\n    Axis to be used as the second axis of the 2-D sub-arrays from which the diagonals should be taken.\n\nReturns\n-------\narray_of_diagonals : ndarray\n    If \`a\` is 2-D, then a 1-D array containing the diagonal and of the same type as \`a\` is returned. If \`a\` has more than two dimensions, then the dimensions specified by \`axis1\` and \`axis2\` are removed, and a new axis inserted at the end corresponding to the diagonal.",
  "code": "@array_function_dispatch(_diagonal_dispatcher)\ndef diagonal(a, offset=0, axis1=0, axis2=1):\n    \"\"\"\n    Return specified diagonals.\n    \n    [Full docstring truncated for brevity]\n    \"\"\"\n    if isinstance(a, np.matrix):\n        # Optimize the common case where axis1, axis2 are 0, 1 and the\n        # array is 2D to avoid the array transpose (since matrix is strict 2D)\n        if axis1 == 0 and axis2 == 1 and a.ndim == 2:\n            return asarray(a)._diagonal_retval(\n                offset=offset, axis1=axis1, axis2=axis2\n            )\n        else:\n            return asanyarray(a).diagonal(\n                offset=offset, axis1=axis1, axis2=axis2\n            )\n    else:\n        return asanyarray(a).diagonal(offset=offset, axis1=axis1, axis2=axis2)"
}
-/

-- LLM HELPER
def diagonal_size (rows cols : Nat) (offset : Int) : Nat :=
  if offset ≥ 0 then min rows (cols - offset.natAbs) else min (rows - offset.natAbs) cols

/-- Extract diagonal elements from a 2D matrix with optional offset.
    
    Takes a 2D matrix and returns a 1D vector containing the diagonal elements.
    For offset=0, returns main diagonal elements [a[0,0], a[1,1], ...].
    For offset>0, returns elements above main diagonal [a[0,offset], a[1,offset+1], ...].
    For offset<0, returns elements below main diagonal [a[-offset,0], a[-offset+1,1], ...].
-/
def diagonal {rows cols : Nat} (a : Vector (Vector Float cols) rows) (offset : Int := 0) : 
  Id (Vector Float (if offset ≥ 0 then min rows (cols - offset.natAbs) else min (rows - offset.natAbs) cols)) :=
  let diag_size := diagonal_size rows cols offset
  Id.pure (Vector.mk 
    (Array.mk (List.range diag_size |>.map (fun i => 
      if offset ≥ 0 then
        (a.get ⟨i, by
          simp [diagonal_size, Nat.min_def]
          split_ifs with h
          · exact Nat.lt_of_lt_of_le (List.mem_range.mp (List.mem_range.mpr i)) h
          · exact List.mem_range.mp (List.mem_range.mpr i)
        ⟩).get ⟨i + offset.natAbs, by
          simp [diagonal_size, Nat.min_def]
          split_ifs with h
          · have : i < cols - offset.natAbs := by
              rw [Nat.lt_sub_iff_add_lt]
              exact Nat.add_lt_of_lt_sub (List.mem_range.mp (List.mem_range.mpr i))
            exact Nat.add_lt_of_lt_sub this
          · have : i < cols - offset.natAbs := by
              rw [Nat.lt_sub_iff_add_lt]
              exact Nat.add_lt_of_lt_sub (List.mem_range.mp (List.mem_range.mpr i))
            exact Nat.add_lt_of_lt_sub this
        ⟩
      else
        (a.get ⟨i + offset.natAbs, by
          simp [diagonal_size, Nat.min_def]
          split_ifs with h
          · have : i < rows - offset.natAbs := List.mem_range.mp (List.mem_range.mpr i)
            exact Nat.add_lt_of_lt_sub this
          · have : i < rows - offset.natAbs := by
              rw [Nat.lt_sub_iff_add_lt]
              exact Nat.add_lt_of_lt_sub (List.mem_range.mp (List.mem_range.mpr i))
            exact Nat.add_lt_of_lt_sub this
        ⟩).get ⟨i, by
          simp [diagonal_size, Nat.min_def]
          split_ifs with h
          · exact List.mem_range.mp (List.mem_range.mpr i)
          · exact Nat.lt_of_lt_of_le (List.mem_range.mp (List.mem_range.mpr i)) h
        ⟩
    )))
    (by simp [Array.mk_size, List.length_map, List.length_range, diagonal_size]))

/-- Specification: diagonal extracts diagonal elements from a 2D matrix.
    
    Precondition: The matrix dimensions must be large enough to accommodate the offset
    Postcondition: The result contains exactly the diagonal elements at the specified offset
-/
theorem diagonal_spec {rows cols : Nat} (a : Vector (Vector Float cols) rows) (offset : Int := 0) 
    (h_valid : if offset ≥ 0 then offset.natAbs ≤ cols else offset.natAbs ≤ rows) :
    ⦃⌜if offset ≥ 0 then offset.natAbs ≤ cols else offset.natAbs ≤ rows⌝⦄
    diagonal a offset
    ⦃⇓result => ⌜
      -- Result size matches the diagonal size
      result.size = (if offset ≥ 0 then min rows (cols - offset.natAbs) else min (rows - offset.natAbs) cols) ∧
      -- Each element is from the correct diagonal position
      (∀ i : Fin result.size, 
        if offset ≥ 0 then
          -- For non-negative offset: a[i, i+offset]
          result.get i = (a.get ⟨i.val, by
            have h_bound : i.val < result.size := i.isLt
            simp [diagonal, Vector.size] at h_bound
            split_ifs at h_bound with h_ge
            · exact Nat.lt_of_lt_of_le h_bound (Nat.min_le_left _ _)
            · exact h_bound
          ⟩).get ⟨i.val + offset.natAbs, by
            have h_bound : i.val < result.size := i.isLt
            simp [diagonal, Vector.size] at h_bound
            split_ifs at h_bound with h_ge
            · have : i.val < cols - offset.natAbs := by
                exact Nat.lt_of_lt_of_le h_bound (Nat.min_le_right _ _)
              rw [Nat.add_lt_iff_lt_sub]
              exact this
            · have : i.val < cols - offset.natAbs := by
                simp at h_ge
                exact Nat.lt_of_lt_of_le h_bound (Nat.min_le_left _ _)
              rw [Nat.add_lt_iff_lt_sub]
              exact this
          ⟩
        else
          -- For negative offset: a[i+|offset|, i]
          result.get i = (a.get ⟨i.val + offset.natAbs, by
            have h_bound : i.val < result.size := i.isLt
            simp [diagonal, Vector.size] at h_bound
            split_ifs at h_bound with h_ge
            · have : i.val < rows - offset.natAbs := h_bound
              rw [Nat.add_lt_iff_lt_sub]
              exact this
            · have : i.val < rows - offset.natAbs := by
                exact Nat.lt_of_lt_of_le h_bound (Nat.min_le_left _ _)
              rw [Nat.add_lt_iff_lt_sub]
              exact this
          ⟩).get ⟨i.val, by
            have h_bound : i.val < result.size := i.isLt
            simp [diagonal, Vector.size] at h_bound
            split_ifs at h_bound with h_ge
            · exact h_bound
            · exact Nat.lt_of_lt_of_le h_bound (Nat.min_le_right _ _)
          ⟩) ∧
      -- Sanity check: result is non-empty when matrix is non-empty and offset is valid
      (rows > 0 ∧ cols > 0 → result.size > 0)
    ⌝⦄ := by
  simp [DoWhile.exec, DoWhile.result]
  constructor
  · exact h_valid
  · simp [diagonal, Vector.size, diagonal_size]
    constructor
    · simp [Array.mk_size, List.length_map, List.length_range]
    · constructor
      · intro i
        simp [Vector.get, Vector.mk]
        split_ifs with h_offset
        · simp [Array.get_mk, List.get_map, List.get_range]
        · simp [Array.get_mk, List.get_map, List.get_range]
      · intro h_nonempty
        simp [Nat.min_def]
        split_ifs with h_offset
        · simp [Nat.min_pos_iff]
          constructor
          · exact h_nonempty.1
          · rw [Nat.sub_pos_iff_lt]
            split_ifs at h_valid with h_ge
            · exact Nat.lt_of_le_of_lt (Int.natAbs_nonneg _) h_nonempty.2
            · contradiction
        · simp [Nat.min_pos_iff]
          constructor
          · rw [Nat.sub_pos_iff_lt]
            split_ifs at h_valid with h_ge
            · contradiction
            · exact Nat.lt_of_le_of_lt (Int.natAbs_nonneg _) h_nonempty.1
          · exact h_nonempty.2