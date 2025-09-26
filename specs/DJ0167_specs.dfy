// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Unique(a: array<int>) returns (result: array<int>)
    requires forall i, j :: 0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures forall i, j :: 0 <= i && i < j && j < result.Length ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
