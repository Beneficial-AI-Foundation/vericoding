

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
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[k]) + 1
    invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
  {
    a[i] := a[i] + 1;
  }
}
// </vc-code>

