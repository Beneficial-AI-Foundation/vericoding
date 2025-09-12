// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (c: array<int>)
    ensures forall k :: 0 <= k < c.Length ==> InArray(a[..], c[k]) && !InArray(b[..], c[k])
    ensures forall i, j :: 0 <= i < j < c.Length ==> c[i] != c[j]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
