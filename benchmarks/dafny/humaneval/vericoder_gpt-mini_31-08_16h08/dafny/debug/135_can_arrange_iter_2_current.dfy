

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (pos: int)
  // pre-conditions-start
  requires |arr| > 0
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
  // pre-conditions-end
  // post-conditions-start
  ensures pos == -1 ==> forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i - 1]
  ensures pos >= 0 ==> 1 <= pos < |arr| && arr[pos] < arr[pos - 1]
  ensures pos >= 0 ==> forall i :: pos < i < |arr| ==> arr[i] >= arr[i - 1]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |arr|;
  var i := n - 1;
  while i > 0
    invariant 0 <= i < n
    invariant forall k :: i < k < n ==> arr[k] >= arr[k - 1]
    decreases i
  {
    if arr[i] < arr[i - 1] {
      return i;
    }
    i := i - 1;
  }
  return -1;
}
// </vc-code>

