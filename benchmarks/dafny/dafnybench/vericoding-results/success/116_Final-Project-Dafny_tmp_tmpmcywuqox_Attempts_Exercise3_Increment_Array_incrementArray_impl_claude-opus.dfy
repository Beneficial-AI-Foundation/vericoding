

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j]) + 1
    invariant forall j :: i <= j < a.Length ==> a[j] == old(a[j])
  {
    a[i] := a[i] + 1;
    i := i + 1;
  }
}
// </vc-code>

