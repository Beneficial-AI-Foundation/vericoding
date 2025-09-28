// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }

function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxDifference(arr: array<int>) returns (diff: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] - arr[j] <= diff
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  var i := 1;
  var minv := arr[0];
  var maxv := arr[0];
  while i < n
    invariant 1 <= i <= n
    invariant minv <= maxv
    invariant forall k :: 0 <= k < i ==> arr[k] <= maxv
    invariant forall k :: 0 <= k < i ==> minv <= arr[k]
    decreases n - i
  {
    if arr[i] < minv {
      minv := arr[i];
    }
    if arr[i] > maxv {
      maxv := arr[i];
    }
    i := i + 1;
  }
  diff := maxv - minv;
  assert forall k :: 0 <= k < n ==> arr[k] <= maxv;
  assert forall k :: 0 <= k < n ==> minv <= arr[k];
  assert forall p, q :: 0 <= p < n && 0 <= q < n ==> arr[p] - arr[q] <= diff;
}
// </vc-code>
