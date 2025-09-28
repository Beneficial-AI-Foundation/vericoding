// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures (result >= 0 ==> (
        0 <= result < arr.Length &&
        arr[result] == target &&
        forall i :: 0 <= i < result ==> arr[i] != target
    )) &&
    (result == -1 ==> (
        forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> arr[k] != target
  {
    if arr[i] == target {
      result := i;
      return;
    }
    i := i + 1;
  }
  result := -1;
}
// </vc-code>
