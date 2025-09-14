

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
// </vc-spec>
// <vc-code>
{
  r := a[0];
  var idx := 0;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= idx < i
    invariant r == a[idx]
    invariant forall k :: 0 <= k < i ==> r <= a[k]
    decreases a.Length - i
  {
    if a[i] < r {
      idx := i;
      r := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>

