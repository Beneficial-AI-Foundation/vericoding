import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.argwhere",
  "category": "Boolean/mask indexing",
  "description": "Find the indices of array elements that are non-zero, grouped by element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argwhere.html",
  "doc": "Find the indices of array elements that are non-zero, grouped by element.\n\nParameters\n----------\na : array_like\n    Input data.\n\nReturns\n-------\nindex_array : (N, a.ndim) ndarray\n    Indices of elements that are non-zero. Indices are grouped by element.\n    This array will have shape \`\`(N, a.ndim)\`\` where \`\`N\`\` is the number of\n    non-zero items.\n\nNotes\n-----\n\`\`np.argwhere(a)\`\` is almost the same as \`\`np.transpose(np.nonzero(a))\`\`, but produces the correct result for a 0D array.\n\nThe output of \`\`argwhere\`\` is not suitable for indexing arrays. For this purpose use \`\`nonzero(a)\`\` instead.",
  "code": "@array_function_dispatch(_argwhere_dispatcher)\ndef argwhere(a):\n    \"\"\"\n    Find the indices of array elements that are non-zero, grouped by element.\n\n    Parameters\n    ----------\n    a : array_like\n        Input data.\n\n    Returns\n    -------\n    index_array : (N, a.ndim) ndarray\n        Indices of elements that are non-zero. Indices are grouped by element.\n        This array will have shape \`\`(N, a.ndim)\`\` where \`\`N\`\` is the number of\n        non-zero items.\n\n    See Also\n    --------\n    where, nonzero\n\n    Notes\n    -----\n    \`\`np.argwhere(a)\`\` is almost the same as \`\`np.transpose(np.nonzero(a))\`\`,\n    but produces the correct result for a 0D array.\n\n    The output of \`\`argwhere\`\` is not suitable for indexing arrays.\n    For this purpose use \`\`nonzero(a)\`\` instead.\n    \"\"\"\n    # nonzero does not behave well on 0d, so promote to 1d\n    if np.ndim(a) == 0:\n        a = shape_base.atleast_1d(a)\n        # then remove the added dimension\n        return argwhere(a)[:, :0]\n    return transpose(nonzero(a))"
}
-/

open Std.Do

/-- numpy.argwhere: Find the indices of array elements that are non-zero, grouped by element.

    For a 1D vector, returns a list of indices where elements are non-zero.
    Each index corresponds to a position in the original vector where the element is non-zero.
    The returned indices are in the same order as they appear in the original vector.
    
    This function is equivalent to finding all positions i such that a[i] ≠ 0.
    The result is a list of indices, not suitable for direct array indexing but useful
    for analysis and conditional processing.
-/
def argwhere {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  sorry

/-- Specification: numpy.argwhere returns all indices of non-zero elements.

    Precondition: True (no special requirements)
    Postcondition: 
    1. All returned indices correspond to non-zero elements in the input vector
    2. All non-zero elements in the input vector have their indices in the result (completeness)
    3. The result contains no duplicate indices
    4. The indices are ordered according to their position in the original vector
    5. The result is empty if and only if all elements in the input are zero
-/
theorem argwhere_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    argwhere a
    ⦃⇓indices => ⌜
      (∀ i ∈ indices, a.get i ≠ 0) ∧
      (∀ i : Fin n, a.get i ≠ 0 → i ∈ indices) ∧
      (indices.Nodup) ∧
      (∀ i j : Fin n, i ∈ indices → j ∈ indices → i < j → 
        indices.idxOf i < indices.idxOf j) ∧
      (indices = [] ↔ ∀ i : Fin n, a.get i = 0)
    ⌝⦄ := by
  sorry
