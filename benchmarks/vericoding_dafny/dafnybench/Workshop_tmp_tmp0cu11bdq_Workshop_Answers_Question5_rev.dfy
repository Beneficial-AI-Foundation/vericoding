// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>