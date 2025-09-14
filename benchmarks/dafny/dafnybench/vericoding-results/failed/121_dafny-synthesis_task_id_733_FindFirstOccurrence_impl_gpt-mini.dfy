

// <vc-helpers>
// Added no-op helper to keep helpers section non-empty and assist verification if needed.
ghost method {:hint} Helper_NoOp()
{
  // Intentionally left empty.
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  if n == 0 {
    index := -1;
    return;
  }
  var lo := 0;
  var hi := n;
  while lo < hi
    invariant 0 <= lo <= hi <= n
    invariant forall i :: 0 <= i < lo ==> arr[i] < target
    invariant forall i :: hi <= i < n ==> arr[i] >= target
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if arr[mid] < target {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  if lo < n && arr[lo] == target {
    index := lo;
  } else {
    index := -1;
  }
}
// </vc-code>

