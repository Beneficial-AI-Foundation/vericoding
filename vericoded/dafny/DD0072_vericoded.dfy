

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
  r := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> r <= a[j]
    invariant exists j :: 0 <= j < i && r == a[j]
  {
    if a[i] < r {
      r := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>

