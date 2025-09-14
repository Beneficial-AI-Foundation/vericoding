// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var low := 0;
  var high := arr.Length;
  while low < high
    invariant 0 <= low <= high <= arr.Length
    invariant forall i :: 0 <= i < low ==> arr[i] < target
    invariant forall i :: high <= i < arr.Length ==> arr[i] >= target
    decreases high - low
  {
    var mid := (low + high) / 2;
    if arr[mid] < target {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  if low < arr.Length && arr[low] == target {
    result := low;
  } else {
    result := -1;
  }
}
// </vc-code>
