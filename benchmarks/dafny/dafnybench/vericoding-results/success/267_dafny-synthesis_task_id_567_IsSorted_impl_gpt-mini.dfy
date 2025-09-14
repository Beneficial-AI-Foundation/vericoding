

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i + 1 < a.Length
    invariant 0 <= i < a.Length
    invariant forall p, q :: 0 <= p < q <= i ==> a[p] <= a[q]
    decreases a.Length - i
  {
    if a[i] > a[i+1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

