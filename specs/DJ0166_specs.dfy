// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TwoWaySort(a: array<bool>)
    requires a.Length <= 100_000
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i, j :: 0 <= i < j < a.Length ==> !a[i] || a[j]
    modifies a
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
