// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method replace(a: array<int>, x: int, y: int)
    modifies a
    ensures
        forall k :: 0 <= k < a.Length && old(a[k]) == x ==> a[k] == y
    ensures
        forall k :: 0 <= k < a.Length && old(a[k]) != x ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i && old(a[k]) == x ==> a[k] == y
    invariant forall k :: 0 <= k < i && old(a[k]) != x ==> a[k] == old(a[k])
    invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
  {
    if a[i] == x {
      a[i] := y;
    }
    i := i + 1;
  }
}
// </vc-code>
