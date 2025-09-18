// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsLastOccurrence(arr: array<int>, elem: int, index: int)
  reads arr
  requires 0 <= index < arr.Length
{
  arr[index] == elem && (forall k :: index < k < arr.Length ==> arr[k] != elem)
}
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
  result := -1;
  var i := arr.Length - 1;
  while i >= 0
    invariant -1 <= i < arr.Length
    invariant forall k :: i < k < arr.Length ==> arr[k] != elem
    decreases i
  {
    if arr[i] == elem {
      result := i;
      return;
    }
    i := i - 1;
  }
}
// </vc-code>
