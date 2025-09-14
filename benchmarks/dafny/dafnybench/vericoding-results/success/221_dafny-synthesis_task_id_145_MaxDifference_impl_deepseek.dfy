

// <vc-helpers>
lemma MaxMinLemma(a: array<int>, min: int, max: int)
  requires a.Length > 0
  requires forall i :: 0 <= i < a.Length ==> min <= a[i] <= max
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= max - min
{
}
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
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> min <= a[k] <= max
    invariant min <= a[i-1] <= max
  {
    if a[i] < min {
      min := a[i];
    }
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
  
  diff := max - min;
  MaxMinLemma(a, min, max);
}
// </vc-code>

