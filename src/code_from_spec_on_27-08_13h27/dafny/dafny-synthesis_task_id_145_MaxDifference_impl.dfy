// <vc-helpers>
// Helper lemma to prove properties about maximum and minimum values in the array
lemma MaxMinDifferenceLemma(a: array<int>, maxVal: int, minVal: int)
  requires a.Length > 1
  requires forall i :: 0 <= i < a.Length ==> a[i] <= maxVal
  requires forall i :: 0 <= i < a.Length ==> a[i] >= minVal
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= maxVal - minVal
{
  forall i, j | 0 <= i < a.Length && 0 <= j < a.Length
  {
    assert a[i] <= maxVal;
    assert a[j] >= minVal;
    assert a[i] - a[j] <= maxVal - minVal;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeMaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 1
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
  var maxVal := a[0];
  var minVal := a[0];
  
  for i := 1 to a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= maxVal
    invariant forall k :: 0 <= k < i ==> a[k] >= minVal
  {
    if a[i] > maxVal {
      maxVal := a[i];
    }
    if a[i] < minVal {
      minVal := a[i];
    }
  }
  
  diff := maxVal - minVal;
  MaxMinDifferenceLemma(a, maxVal, minVal);
}
// </vc-code>
