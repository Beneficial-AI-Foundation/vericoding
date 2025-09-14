

// <vc-helpers>
lemma lemma_array_set_same_except_at_indices<T>(
  a: array<T>, 
  i: int, j: int, 
  x: T, y: T
)
  // This lemma is illustrative. For simple array swaps, Dafny's SMT solver
  // is often sufficient without explicit array lemmas. It would typically be used
  // in a context where an array 'b' is constructed from 'a' with specific elements
  // changed, and we need to prove properties about 'b' relative to 'a'.
  // However, in this specific swap scenario, the direct postconditions of the `swap` method
  // are what need to be proven.
  // The original lemma signature was misleading as it implied properties of 'a' *after*
  // modifications which are handled by the main method's postconditions, not by a lemma describing 
  // ideal conditions. Therefore, this lemma is removed as it does not contribute to the verification
  // of the `swap` method itself and was causing confusion with its `ensures` clause.
// </vc-helpers>

// <vc-spec>
method swap(arr: array<int>, i: int, j: int)
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
// </vc-spec>
// <vc-code>
{
  var temp_i := arr[i];
  var temp_j := arr[j];

  arr[i] := temp_j;
  arr[j] := temp_i;
}
// </vc-code>

