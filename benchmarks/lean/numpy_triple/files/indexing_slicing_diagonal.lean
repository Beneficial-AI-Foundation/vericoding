/- 
{
  "name": "numpy.diagonal",
  "category": "Diagonal operations",
  "description": "Return specified diagonals",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diagonal.html",
  "doc": "Return specified diagonals.\n\nIf \`a\` is 2-D, returns the diagonal of \`a\` with the given offset, i.e., the collection of elements of the form \`\`a[i, i+offset]\`\`. If \`a\` has more than two dimensions, then the axes specified by \`axis1\` and \`axis2\` are used to determine the 2-D sub-array whose diagonal is returned. The shape of the resulting array can be determined by removing \`axis1\` and \`axis2\` and appending an index to the right equal to the size of the resulting diagonals.\n\nParameters\n----------\na : array_like\n    Array from which the diagonals are taken.\noffset : int, optional\n    Offset of the diagonal from the main diagonal. Can be positive or negative.\naxis1 : int, optional\n    Axis to be used as the first axis of the 2-D sub-arrays from which the diagonals should be taken.\naxis2 : int, optional\n    Axis to be used as the second axis of the 2-D sub-arrays from which the diagonals should be taken.\n\nReturns\n-------\narray_of_diagonals : ndarray\n    If \`a\` is 2-D, then a 1-D array containing the diagonal and of the same type as \`a\` is returned. If \`a\` has more than two dimensions, then the dimensions specified by \`axis1\` and \`axis2\` are removed, and a new axis inserted at the end corresponding to the diagonal.",
}
-/

/-  Extract diagonal elements from a 2D matrix with optional offset.
    
    Takes a 2D matrix and returns a 1D vector containing the diagonal elements.
    For offset=0, returns main diagonal elements [a[0,0], a[1,1], ...].
    For offset>0, returns elements above main diagonal [a[0,offset], a[1,offset+1], ...].
    For offset<0, returns elements below main diagonal [a[-offset,0], a[-offset+1,1], ...].
-/

/-  Specification: diagonal extracts diagonal elements from a 2D matrix.
    
    Precondition: The matrix dimensions must be large enough to accommodate the offset
    Postcondition: The result contains exactly the diagonal elements at the specified offset
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def diagonal {rows cols : Nat} (a : Vector (Vector Float cols) rows) (offset : Int := 0) : 
  Id (Vector Float (if offset ≥ 0 then min rows (cols - offset.natAbs) else min (rows - offset.natAbs) cols)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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
          result.get i = (a.get ⟨i.val, by sorry⟩).get ⟨i.val + offset.natAbs, by sorry⟩
        else
          -- For negative offset: a[i+|offset|, i]
          result.get i = (a.get ⟨i.val + offset.natAbs, by sorry⟩).get ⟨i.val, by sorry⟩) ∧
      -- Sanity check: result is non-empty when matrix is non-empty and offset is valid
      (rows > 0 ∧ cols > 0 → result.size > 0)
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
