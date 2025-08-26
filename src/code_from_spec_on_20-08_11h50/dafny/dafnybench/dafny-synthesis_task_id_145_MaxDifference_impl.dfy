method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
  var max := a[0];
  var min := a[0];
  var k := 1;
  
  while k < a.Length
    invariant 1 <= k <= a.Length
    invariant forall i :: 0 <= i < k ==> a[i] <= max
    invariant forall i :: 0 <= i < k ==> min <= a[i]
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