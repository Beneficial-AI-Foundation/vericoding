

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
  var m := a[0];
  var idx := 0;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= idx < i
    invariant m == a[idx]
    invariant forall j :: 0 <= j < i ==> m <= a[j]
    decreases a.Length - i
  {
    if a[i] < m {
      m := a[i];
      idx := i;
    }
    i := i + 1;
  }
  r := m;
}
// </vc-code>

