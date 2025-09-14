

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires a.Length > 0
  ensures 0<= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
// </vc-spec>
// <vc-code>
{
  var maxIdx := 0;
  var j := 1;
  while j < a.Length
    invariant 0 <= maxIdx < a.Length
    invariant 1 <= j <= a.Length
    invariant forall t :: 0 <= t < j ==> a[t] <= a[maxIdx]
    decreases a.Length - j
  {
    if a[j] > a[maxIdx] {
      maxIdx := j;
    }
    j := j + 1;
  }
  i := maxIdx;
}
// </vc-code>

