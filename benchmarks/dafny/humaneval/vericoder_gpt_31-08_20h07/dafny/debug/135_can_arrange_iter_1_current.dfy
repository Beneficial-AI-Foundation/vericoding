

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
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
  var i := 1;
  var lastInv := -1;
  while i < n
    invariant 1 <= i <= n
    invariant -1 <= lastInv < i
    invariant lastInv == -1 || 1 <= lastInv
    invariant lastInv >= 1 ==> arr[lastInv] < arr[lastInv - 1]
    invariant forall j :: 1 <= j < i ==> lastInv < j ==> arr[j] >= arr[j - 1]
    decreases n - i
  {
    if arr[i] < arr[i - 1] {
      lastInv := i;
    }
    i := i + 1;
  }
  pos := lastInv;
}
// </vc-code>

