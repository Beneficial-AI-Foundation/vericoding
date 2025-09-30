// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }

function min(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxDifference(arr: array<int>) returns (diff: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] - arr[j] <= diff
// </vc-spec>
// <vc-code>
{
  var maxVal := arr[0];
  var minVal := arr[0];
  var i := 1;
  
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> arr[k] <= maxVal
    invariant forall k :: 0 <= k < i ==> arr[k] >= minVal
    invariant exists k :: 0 <= k < i && arr[k] == maxVal
    invariant exists k :: 0 <= k < i && arr[k] == minVal
  {
    maxVal := max(maxVal, arr[i]);
    minVal := min(minVal, arr[i]);
    i := i + 1;
  }
  
  diff := maxVal - minVal;
}
// </vc-code>
