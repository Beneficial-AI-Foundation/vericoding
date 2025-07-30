import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.partition",
  "category": "Sorting", 
  "description": "Return a partitioned copy of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.partition.html",
  "doc": "Return a partitioned copy of an array.\n\nCreates a copy of the array with its elements rearranged in such a way that\nthe value of the element in k-th position is in the position it would be in\na sorted array. All elements smaller than the k-th element are moved before\nthis element and all equal or greater are moved behind it. The ordering of\nthe elements in the two partitions is undefined.\n\nParameters\n----------\na : array_like\n    Array to be sorted.\nkth : int or sequence of ints\n    Element index to partition by. The k-th value of the element will be in\n    its final sorted position and all smaller elements will be moved before it\n    and all equal or greater elements behind it. The order of all elements in\n    the partitions is undefined. If provided with a sequence of k-th it will\n    partition all elements indexed by k-th of them into their sorted position\n    at once.\naxis : int or None, optional\n    Axis along which to sort. If None, the array is flattened before sorting.\n    The default is -1, which sorts along the last axis.\nkind : {'introselect'}, optional\n    Selection algorithm. Default is 'introselect'.\norder : str or list of str, optional\n    When \`a\` is an array with fields defined, this argument specifies which\n    fields to compare first, second, etc.\n\nReturns\n-------\npartitioned_array : ndarray\n    Array of the same type and shape as \`a\`.",
  "code": "@array_function_dispatch(_partition_dispatcher)\ndef partition(a, kth, axis=-1, kind='introselect', order=None):\n    \"\"\"\n    Return a partitioned copy of an array.\n\n    Creates a copy of the array with its elements rearranged in such a way that\n    the value of the element in k-th position is in the position it would be in\n    a sorted array. All elements smaller than the k-th element are moved before\n    this element and all equal or greater are moved behind it. The ordering of\n    the elements in the two partitions is undefined.\n\n    .. versionadded:: 1.8.0\n\n    Parameters\n    ----------\n    a : array_like\n        Array to be sorted.\n    kth : int or sequence of ints\n        Element index to partition by. The k-th value of the element will be in\n        its final sorted position and all smaller elements will be moved before it\n        and all equal or greater elements behind it. The order of all elements in\n        the partitions is undefined. If provided with a sequence of k-th it will\n        partition all elements indexed by k-th of them into their sorted position\n        at once.\n    axis : int or None, optional\n        Axis along which to sort. If None, the array is flattened before sorting.\n        The default is -1, which sorts along the last axis.\n    kind : {'introselect'}, optional\n        Selection algorithm. Default is 'introselect'.\n    order : str or list of str, optional\n        When \`a\` is an array with fields defined, this argument specifies which\n        fields to compare first, second, etc. A single field can be specified\n        as a string. Not all fields need be specified, but unspecified fields\n        will still be used, in the order in which they come up in the dtype,\n        to break ties.\n\n    Returns\n    -------\n    partitioned_array : ndarray\n        Array of the same type and shape as \`a\`.\n\n    See Also\n    --------\n    ndarray.partition : Method to sort an array in-place.\n    argpartition : Indirect partition.\n    sort : Full sorting\n\n    \"\"\"\n    if axis is None:\n        # flatten returns (1, N) for np.matrix, so always use the last axis\n        a = asanyarray(a).flatten()\n        axis = -1\n    else:\n        a = asanyarray(a).copy(order=\"K\")\n    a.partition(kth, axis=axis, kind=kind, order=order)\n    return a"
}
-/

open Std.Do

/-- Return a partitioned copy of an array around the k-th element -/
def partition {n : Nat} (arr : Vector Float n) (kth : Fin n) : Id (Vector Float n) :=
  sorry

/-- Specification: partition rearranges elements so that the k-th element is in its sorted position,
    with smaller elements before it and equal/greater elements after it -/
theorem partition_spec {n : Nat} (arr : Vector Float n) (kth : Fin n) :
    ⦃⌜True⌝⦄
    partition arr kth
    ⦃⇓result => ⌜
      -- All elements before kth are ≤ the kth element
      (∀ i : Fin n, i < kth → result.get i ≤ result.get kth) ∧
      -- All elements after kth are ≥ the kth element  
      (∀ i : Fin n, kth < i → result.get i ≥ result.get kth) ∧
      -- The k-th element is in its correct sorted position relative to the original array
      (∃ (sorted : Vector Float n), 
        (∀ i j : Fin n, i < j → sorted.get i ≤ sorted.get j) ∧
        (∀ i : Fin n, ∃ j : Fin n, sorted.get i = arr.get j) ∧
        (∀ i : Fin n, ∃ j : Fin n, arr.get i = sorted.get j) ∧
        result.get kth = sorted.get kth) ∧
      -- The result contains the same elements as the original (multiset equality)
      (∀ x : Float, (List.ofFn (fun i => result.get i)).count x = (List.ofFn (fun i => arr.get i)).count x)
    ⌝⦄ := by
  sorry