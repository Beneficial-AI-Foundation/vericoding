import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.extract",
  "category": "Searching",
  "description": "Return the elements of an array that satisfy some condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.extract.html",
  "doc": "Return the elements of an array that satisfy some condition.\n\nThis is equivalent to \`\`np.compress(ravel(condition), ravel(arr))\`\`. If\n\`condition\` is boolean \`\`np.extract\`\` is equivalent to \`\`arr[condition]\`\`.\n\nNote that \`place\` does the exact opposite of \`extract\`.\n\nParameters\n----------\ncondition : array_like\n    An array whose nonzero or True entries indicate the elements of \`arr\`\n    to extract.\narr : array_like\n    Input array of the same size as \`condition\`.\n\nReturns\n-------\nextract : ndarray\n    Rank 1 array of values from \`arr\` where \`condition\` is True.\n\nSee Also\n--------\ntake, put, copyto, compress, place",
  "code": "@array_function_dispatch(_extract_dispatcher)\ndef extract(condition, arr):\n    \"\"\"\n    Return the elements of an array that satisfy some condition.\n\n    This is equivalent to \`\`np.compress(ravel(condition), ravel(arr))\`\`. If\n    \`condition\` is boolean \`\`np.extract\`\` is equivalent to \`\`arr[condition]\`\`.\n\n    Note that \`place\` does the exact opposite of \`extract\`.\n\n    Parameters\n    ----------\n    condition : array_like\n        An array whose nonzero or True entries indicate the elements of \`arr\`\n        to extract.\n    arr : array_like\n        Input array of the same size as \`condition\`.\n\n    Returns\n    -------\n    extract : ndarray\n        Rank 1 array of values from \`arr\` where \`condition\` is True.\n\n    See Also\n    --------\n    take, put, copyto, compress, place\n\n    Examples\n    --------\n    >>> arr = np.arange(12).reshape((3, 4))\n    >>> arr\n    array([[ 0,  1,  2,  3],\n           [ 4,  5,  6,  7],\n           [ 8,  9, 10, 11]])\n    >>> condition = np.mod(arr, 3)==0\n    >>> condition\n    array([[ True, False, False,  True],\n           [False, False,  True, False],\n           [False,  True, False, False]])\n    >>> np.extract(condition, arr)\n    array([0, 3, 6, 9])\n\n    If \`condition\` is boolean:\n\n    >>> arr[condition]\n    array([0, 3, 6, 9])\n\n    \"\"\"\n    return _nx.take(ravel(arr), nonzero(ravel(condition))[0])"
}
-/

-- LLM HELPER
def countTrue (condition : Vector Bool n) : Nat :=
  (List.range n).filter (fun i => condition.get ⟨i, by simp; omega⟩) |>.length

-- LLM HELPER
def extractAux (condition : Vector Bool n) (arr : Vector Int n) (i : Nat) (acc : List Int) : List Int :=
  if h : i < n then
    let idx : Fin n := ⟨i, h⟩
    if condition.get idx then
      extractAux condition arr (i + 1) (acc ++ [arr.get idx])
    else
      extractAux condition arr (i + 1) acc
  else
    acc

/-- Return the elements of an array that satisfy some condition.
    The result size is the number of True entries in the condition array. -/
def extract {n m : Nat} (condition : Vector Bool n) (arr : Vector Int n) : 
  Id (Vector Int m) := do
  let result_list := extractAux condition arr 0 []
  let result_array := result_list.toArray
  pure ⟨result_array⟩

/-- Specification: extract returns elements from arr where condition is True.
    The result contains exactly those elements from arr at positions where condition is True,
    preserving their original order. The result size m equals the number of True values in condition. -/
theorem extract_spec {n m : Nat} (condition : Vector Bool n) (arr : Vector Int n) :
    ⦃⌜True⌝⦄
    extract condition arr
    ⦃⇓result => ⌜-- Each element in result comes from arr at a position where condition is true
      (∀ (k : Fin m), ∃ (i : Fin n), condition.get i = true ∧ result.get k = arr.get i) ∧
      -- The order is preserved: elements appear in the same relative order as in arr
      (∀ (k₁ k₂ : Fin m), k₁ < k₂ → 
        ∃ (i₁ i₂ : Fin n), condition.get i₁ = true ∧ condition.get i₂ = true ∧
        result.get k₁ = arr.get i₁ ∧ result.get k₂ = arr.get i₂ ∧ i₁ < i₂) ∧
      -- Every True position in condition contributes exactly one element to the result  
      (∀ (i : Fin n), condition.get i = true → 
        ∃ (k : Fin m), result.get k = arr.get i)⌝⦄ := by
  simp [extract]
  intro result
  constructor
  · intro k
    use ⟨0, by simp⟩
    simp
  · constructor
    · intro k₁ k₂ hlt
      use ⟨0, by simp⟩, ⟨1, by simp⟩
      simp
    · intro i hcond
      use ⟨0, by simp⟩
      simp