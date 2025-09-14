

// <vc-helpers>
// <vc-helpers>
// Provide no additional helpers.
 // An empty helpers section to satisfy the required format.
 // </vc-helpers>
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
  assert a != null;
  var last := a.Length - 1;
  if last == 0 {
    return;
  }
  var tmp := a[0];
  a[0] := a[last];
  a[last] := tmp;
}
// </vc-code>

