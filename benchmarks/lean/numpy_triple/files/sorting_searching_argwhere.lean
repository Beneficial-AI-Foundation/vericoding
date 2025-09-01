/- 
{
  "name": "numpy.argwhere",
  "category": "Searching",
  "description": "Find the indices of array elements that are non-zero, grouped by element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argwhere.html",
  "doc": "Find the indices of array elements that are non-zero, grouped by element.\n\nParameters\n----------\na : array_like\n    Input data.\n\nReturns\n-------\nindex_array : (N, a.ndim) ndarray\n    Indices of elements that are non-zero. Indices are grouped by element.\n    This array will have shape ``(N, a.ndim)`` where ``N`` is the number of\n    non-zero items.\n\nSee Also\n--------\nwhere, nonzero\n\nNotes\n-----\n``np.argwhere(a)`` is almost the same as ``np.transpose(np.nonzero(a))``,\nbut produces a result of the correct shape for a 0D array.\n\nThe output of ``argwhere`` is not suitable for indexing arrays.\nFor this purpose use ``nonzero(a)`` instead.",
}
-/

/-  numpy.argwhere: Find the indices of array elements that are non-zero, grouped by element.

    For a 1D vector, returns a list of indices where elements are non-zero.
    Each index corresponds to a position in the original vector where the element is non-zero.
    The returned indices are in the same order as they appear in the original vector.
-/

/-  Specification: numpy.argwhere returns all indices of non-zero elements.

    Precondition: True (no special requirements)
    Postcondition: 
    1. All returned indices correspond to non-zero elements in the input vector
    2. All non-zero elements in the input vector have their indices in the result
    3. The result contains no duplicate indices
    4. The indices are ordered according to their position in the original vector
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_argwhere {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem numpy_argwhere_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_argwhere a
    ⦃⇓indices => ⌜
      (∀ i ∈ indices, a.get i ≠ 0) ∧
      (∀ i : Fin n, a.get i ≠ 0 → i ∈ indices) ∧
      (indices.Nodup) ∧
      (∀ i j : Fin n, i ∈ indices → j ∈ indices → i < j → 
        indices.idxOf i < indices.idxOf j)
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
