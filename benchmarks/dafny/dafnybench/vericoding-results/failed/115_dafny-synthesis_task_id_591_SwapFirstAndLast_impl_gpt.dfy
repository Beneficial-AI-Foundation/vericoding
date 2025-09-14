

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  var first := a[0];
  var last := a[a.Length - 1];
  a[0] := last;
  a[a.Length - 1] := first;
}
// </vc-code>

