// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause for array access */
predicate Sorted(arr: array<int>) reads arr { forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j] }
// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures
        (result >= 0 ==> 
            0 <= result < arr.Length &&
            arr[result] == elem &&
            forall k :: result < k < arr.Length ==> arr[k] != elem) &&
        (result == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): linear scan maintaining last seen index and safe invariants */
  var i := 0;
  result := -1;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant -1 <= result < arr.Length
    invariant result == -1 || arr[result] == elem
    invariant forall k :: 0 <= k < i && result < k ==> arr[k] != elem
    decreases arr.Length - i
  {
    if arr[i] == elem {
      result := i;
    }
    i := i + 1;
  }
}
// </vc-code>
