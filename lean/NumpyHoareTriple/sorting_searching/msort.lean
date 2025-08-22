import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.msort",
  "category": "Sorting",
  "description": "Return a copy of an array sorted along the first axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.msort.html",
  "doc": "Return a copy of an array sorted along the first axis.\n\n.. deprecated:: 1.24.0\n    msort is deprecated, use \`\`np.sort(a, axis=0)\`\` instead.\n\nParameters\n----------\na : array_like\n    Array to be sorted.\n\nReturns\n-------\nsorted_array : ndarray\n    Array of the same type and shape as \`a\`.\n\nSee Also\n--------\nsort\n\nNotes\n-----\n\`\`np.msort(a)\`\` is equivalent to \`\`np.sort(a, axis=0)\`\`.",
  "code": "@array_function_dispatch(_msort_dispatcher)\ndef msort(a):\n    \"\"\"\n    Return a copy of an array sorted along the first axis.\n\n    .. deprecated:: 1.24.0\n        msort is deprecated, use \`\`np.sort(a, axis=0)\`\` instead.\n\n    Parameters\n    ----------\n    a : array_like\n        Array to be sorted.\n\n    Returns\n    -------\n    sorted_array : ndarray\n        Array of the same type and shape as \`a\`.\n\n    See Also\n    --------\n    sort\n\n    Notes\n    -----\n    \`\`np.msort(a)\`\` is equivalent to \`\`np.sort(a, axis=0)\`\`.\n\n    \"\"\"\n    # 2020-11-19, NumPy 1.20.0\n    warnings.warn(\n        \"\`msort\` is deprecated, use \`np.sort(a, axis=0)\` instead\",\n        DeprecationWarning,\n        stacklevel=2,\n    )\n    b = array(a, subok=True, copy=True)\n    b.sort(0)\n    return b"
}
-/

/-- Return a copy of an array sorted along the first axis (ascending order).
    This is equivalent to np.sort(a, axis=0) in NumPy. -/
def msort {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: msort returns a sorted copy of the input array in ascending order.
    The result is a permutation of the input array. -/
theorem msort_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    msort a
    ⦃⇓result => ⌜
      -- The result is sorted in ascending order
      (∀ i j : Fin n, i.val < j.val → result.get i ≤ result.get j) ∧
      -- The result is a permutation of the input (same multiset of elements)
      (∀ x : Float, (a.toList.count x) = (result.toList.count x))
    ⌝⦄ := by
  sorry