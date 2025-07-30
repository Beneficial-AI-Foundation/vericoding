import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.extract",
  "category": "Boolean/mask indexing",
  "description": "Return the elements of an array that satisfy some condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.extract.html",
  "doc": "Return the elements of an array that satisfy some condition.\n\nThis is equivalent to \`\`np.compress(ravel(condition), ravel(arr))\`\`. If \`condition\` is boolean \`\`np.extract\`\` is equivalent to \`\`arr[condition]\`\`.\n\nNote that \`place\` does the exact opposite of \`extract\`.\n\nParameters\n----------\ncondition : array_like\n    An array whose nonzero or True entries indicate the elements of \`arr\` to extract.\narr : array_like\n    Input array of the same size as \`condition\`.\n\nReturns\n-------\nextract : ndarray\n    Rank 1 array of values from \`arr\` where \`condition\` is True.",
  "code": "@array_function_dispatch(_extract_dispatcher)\ndef extract(condition, arr):\n    \"\"\"\n    Return the elements of an array that satisfy some condition.\n\n    This is equivalent to \`\`np.compress(ravel(condition), ravel(arr))\`\`.  If\n    \`condition\` is boolean \`\`np.extract\`\` is equivalent to \`\`arr[condition]\`\`.\n\n    Note that \`place\` does the exact opposite of \`extract\`.\n\n    Parameters\n    ----------\n    condition : array_like\n        An array whose nonzero or True entries indicate the elements of \`arr\`\n        to extract.\n    arr : array_like\n        Input array of the same size as \`condition\`.\n\n    Returns\n    -------\n    extract : ndarray\n        Rank 1 array of values from \`arr\` where \`condition\` is True.\n    \"\"\"\n    return _nx.take(ravel(arr), nonzero(ravel(condition))[0])"
}
-/

/-- numpy.extract: Return the elements of an array that satisfy some condition.
    
    Extracts elements from an array where the corresponding condition is True.
    Both arrays must have the same size, and the result contains only the elements
    from `arr` where `condition` is True, in the same order they appear in `arr`.
    
    The result size `k` must equal the number of True elements in the condition array.
-/
def extract {n k : Nat} (condition : Vector Bool n) (arr : Vector Float n) 
    (h : k = (condition.toArray.toList.count true)) : Id (Vector Float k) :=
  sorry

/-- Specification: numpy.extract returns elements where condition is True.
    
    Precondition: k equals the count of True elements in condition
    Postcondition: The result contains exactly the elements from arr where condition is True,
                  in the same order they appear in arr.
-/
theorem extract_spec {n k : Nat} (condition : Vector Bool n) (arr : Vector Float n) 
    (h : k = (condition.toArray.toList.count true)) :
    ⦃⌜k = (condition.toArray.toList.count true)⌝⦄
    extract condition arr h
    ⦃⇓result => 
      -- The result contains exactly the elements from arr where condition is True
      ⌜∀ i : Fin k, ∃ idx : Fin n, condition.get idx = true ∧ result.get i = arr.get idx⌝
    ⦄ := by
  sorry