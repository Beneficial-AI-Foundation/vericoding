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
  var lo := 0;
  var hi := arr.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= arr.Length
    invariant forall i :: 0 <= i < lo ==> arr[i] < target
    invariant forall i :: hi <= i < arr.Length ==> arr[i] >= target
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if arr[mid] < target {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  if lo < arr.Length && arr[lo] == target {
    result := lo;
  } else {
    result := -1;
  }
}
// </vc-code>
