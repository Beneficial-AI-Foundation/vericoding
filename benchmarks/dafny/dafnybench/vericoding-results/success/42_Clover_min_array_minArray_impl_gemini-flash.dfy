

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
// </vc-spec>
// <vc-code>
{
  var minVal := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant exists k :: 0 <= k < i && minVal == a[k]
  {
    if a[i] < minVal {
      minVal := a[i];
    }
    i := i + 1;
  }
  return minVal;
}
// </vc-code>

