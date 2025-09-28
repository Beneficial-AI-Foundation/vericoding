// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)

    requires
        forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]

    ensures
        if index >= 0 then (
            && 0 <= index < arr.Length
            && (forall k :: 0 <= k < index ==> arr[k] != target)
            && arr[index] == target
        ) else (
            forall k :: 0 <= k < arr.Length ==> arr[k] != target
        )
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> arr[k] != target
  {
    if arr[i] == target {
      index := i;
      return;
    }
    i := i + 1;
  }
  index := -1;
}
// </vc-code>
