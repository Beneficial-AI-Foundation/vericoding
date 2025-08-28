// <vc-helpers>
// No additional helper code or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires a.Length > 0
  ensures 0<= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindMaxImpl(a: array<int>) returns (i: int)
  requires a.Length > 0
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  i := 0;
  var maxVal := a[0];
  var j := 1;
  
  while j < a.Length
    invariant 0 <= i < a.Length
    invariant 0 <= j <= a.Length
    invariant maxVal == a[i]
    invariant forall k :: 0 <= k < j ==> a[k] <= maxVal
  {
    if a[j] > maxVal {
      i := j;
      maxVal := a[j];
    }
    j := j + 1;
  }
}
// </vc-code>
