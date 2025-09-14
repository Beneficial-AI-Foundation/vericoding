

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
  var min := a[0];
  var max := a[0];
  var k := 1;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant forall t :: 0 <= t < k ==> a[t] <= max && a[t] >= min
    decreases a.Length - k
  {
    if a[k] > max {
      max := a[k];
    }
    if a[k] < min {
      min := a[k];
    }
    k := k + 1;
  }
  diff := max - min;
}
// </vc-code>

