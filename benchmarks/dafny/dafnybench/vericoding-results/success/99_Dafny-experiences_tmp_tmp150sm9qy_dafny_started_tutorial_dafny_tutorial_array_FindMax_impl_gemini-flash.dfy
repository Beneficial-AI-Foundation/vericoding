

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires a.Length > 0
  ensures 0<= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
// </vc-spec>
// <vc-code>
{
    i := 0;
    var currentMax := a[0];
    var k := 1;
    while k < a.Length
        invariant 0 <= i < k
        invariant 0 < k <= a.Length
        invariant forall l :: 0 <= l < k ==> a[l] <= a[i]
    {
        if a[k] > a[i] {
            i := k;
        }
        k := k + 1;
    }
    return i;
}
// </vc-code>

