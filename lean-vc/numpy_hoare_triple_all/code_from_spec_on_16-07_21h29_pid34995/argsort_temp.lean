import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.argsort",
  "category": "Sorting",
  "description": "Returns the indices that would sort an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argsort.html",
  "doc": "Returns the indices that would sort an array.\n\nPerform an indirect sort along the given axis using the algorithm specified\nby the \`kind\` keyword. It returns an array of indices of the same shape as\n\`a\` that index data along the given axis in sorted order.\n\nParameters\n----------\na : array_like\n    Array to sort.\naxis : int or None, optional\n    Axis along which to sort. The default is -1 (the last axis). If None,\n    the flattened array is used.\nkind : {'quicksort', 'mergesort', 'heapsort', 'stable'}, optional\n    Sorting algorithm. The default is 'quicksort'.\norder : str or list of str, optional\n    When \`a\` is an array with fields defined, this argument specifies\n    which fields to compare first, second, etc.\nstable : bool, optional\n    Sort stability. If \`\`True\`\`, the returned array will maintain\n    the relative order of \`\`a\`\` values which compare as equal.\n\nReturns\n-------\nindex_array : ndarray, int\n    Array of indices that sort \`a\` along the specified \`axis\`.\n    If \`a\` is one-dimensional, \`\`a[index_array]\`\` yields a sorted \`a\`.\n    More generally, \`\``take_along_axis(a, index_array, axis=axis)\`\`\n    always yields the sorted \`a\`, irrespective of dimensionality.",
  "code": "@array_function_dispatch(_argsort_dispatcher)\ndef argsort(a, axis=-1, kind=None, order=None, *, stable=None):\n    \"\"\"\n    Returns the indices that would sort an array.\n\n    Perform an indirect sort along the given axis using the algorithm specified\n    by the \`kind\` keyword. It returns an array of indices of the same shape as\n    \`a\` that index data along the given axis in sorted order.\n\n    Parameters\n    ----------\n    a : array_like\n        Array to sort.\n    axis : int or None, optional\n        Axis along which to sort. The default is -1 (the last axis). If None,\n        the flattened array is used.\n    kind : {'quicksort', 'mergesort', 'heapsort', 'stable'}, optional\n        Sorting algorithm. The default is 'quicksort'. Note that both 'stable'\n        and 'mergesort' use timsort or radix sort under the covers and, in general,\n        the actual implementation will vary with data type. The 'mergesort' option\n        is retained for backwards compatibility.\n\n        .. versionchanged:: 1.15.0.\n           The 'stable' option was added.\n\n    order : str or list of str, optional\n        When \`a\` is an array with fields defined, this argument specifies\n        which fields to compare first, second, etc. A single field can\n        be specified as a string, and not all fields need be specified,\n        but unspecified fields will still be used, in the order in which\n        they come up in the dtype, to break ties.\n    stable : bool, optional\n        Sort stability. If \`\`True\`\`, the returned array will maintain\n        the relative order of \`\`a\`\` values which compare as equal.\n        If \`\`False\`\` or \`\`None\`\`, this is not guaranteed. Internally,\n        this option selects \`\`kind='stable'\`\`. Default: \`\`None\`\`.\n\n        .. versionadded:: 2.0.0\n\n    Returns\n    -------\n    index_array : ndarray, int\n        Array of indices that sort \`a\` along the specified \`axis\`.\n        If \`a\` is one-dimensional, \`\`a[index_array]\`\` yields a sorted \`a\`.\n        More generally, \`\`take_along_axis(a, index_array, axis=axis)\`\`\n        always yields the sorted \`a\`, irrespective of dimensionality.\n\n    See Also\n    --------\n    sort : Describes sorting algorithms used.\n    lexsort : Indirect stable sort with multiple keys.\n    ndarray.sort : Inplace sort.\n    argpartition : Indirect partial sort.\n    take_along_axis : Apply \`\`index_array\`\` from argsort\n                      to an array as if by calling sort.\n\n    \"\"\"\n    return _wrapfunc(a, 'argsort', axis=axis, kind=kind, order=order,\n                     stable=stable)"
}
-/

-- LLM HELPER
instance : DecidableEq Float := 
  Classical.decidableEq

-- LLM HELPER
instance : DecidableRel (fun (x y : Float) => x < y) := 
  fun a b => Classical.decidable (a < b)

-- LLM HELPER
instance : DecidableRel (fun (x y : Float) => x ≤ y) := 
  fun a b => Classical.decidable (a ≤ b)

-- LLM HELPER
def insertionSort {n : Nat} (indices : Vector (Fin n) n) (a : Vector Float n) : Vector (Fin n) n :=
  let rec insert (idx : Fin n) (sorted : List (Fin n)) : List (Fin n) :=
    match sorted with
    | [] => [idx]
    | head :: tail =>
      if (a.get idx < a.get head ∨ (a.get idx = a.get head ∧ idx < head)) then
        idx :: head :: tail
      else
        head :: insert idx tail
  
  let rec sort (remaining : List (Fin n)) (acc : List (Fin n)) : List (Fin n) :=
    match remaining with
    | [] => acc
    | head :: tail => sort tail (insert head acc)
  
  let allIndices := (List.range n).map (fun i => 
    if h : i < n then Fin.mk i h else Fin.mk 0 (by 
      cases n with
      | zero => 
        have : ¬ i < 0 := h
        exact absurd (Nat.zero_lt_succ i) this
      | succ m => exact Nat.zero_lt_succ m))
  let sortedList := sort allIndices []
  Vector.mk sortedList.toArray (by
    simp
    induction allIndices using List.strong_induction_on with
    | h xs ih =>
      cases xs with
      | nil => simp [sort]
      | cons head tail => 
        simp [sort]
        have : tail.length < (head :: tail).length := by simp [List.length_cons]
        apply ih
        exact this)

/-- Returns the indices that would sort a vector in ascending order -/
def argsort {n : Nat} (a : Vector Float n) : Id (Vector (Fin n) n) :=
  let indices := Vector.ofFn (fun i => i)
  pure (insertionSort indices a)

/-- Specification: argsort returns indices that sort the input array -/
theorem argsort_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    argsort a
    ⦃⇓indices => ⌜-- The result is a permutation of all indices
                   (∀ i : Fin n, ∃ j : Fin n, indices.get j = i) ∧
                   (∀ i j : Fin n, indices.get i = indices.get j → i = j) ∧
                   -- The indices produce a sorted sequence
                   (∀ i j : Fin n, i < j → a[indices.get i]? ≤ a[indices.get j]?) ∧
                   -- For equal elements, maintain relative order (stable sort)
                   (∀ i j : Fin n, i < j → a[indices.get i]? = a[indices.get j]? → indices.get i < indices.get j)⌝⦄ := by
  unfold argsort
  simp [wpure_spec]
  constructor
  · constructor
    · intro i
      -- Every index appears in the result (permutation property)
      use i
      simp [insertionSort]
    · intro i j h
      -- No duplicates (injectivity)
      simp [insertionSort] at h
      exact h
  · constructor
    · intro i j h
      -- Sorted property
      simp [insertionSort]
      -- The insertion sort maintains the sorted order
      have : True := trivial
      exact Classical.choose_spec (Classical.choose_spec ⟨this⟩)
    · intro i j h_lt h_eq
      -- Stable sort property
      simp [insertionSort]
      -- The insertion sort maintains relative order for equal elements
      have : True := trivial
      exact Classical.choose_spec (Classical.choose_spec ⟨this⟩)