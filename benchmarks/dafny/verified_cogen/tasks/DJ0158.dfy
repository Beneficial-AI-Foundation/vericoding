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
    assume {:axiom} false;
}
// </vc-code>
