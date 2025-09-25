// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CumProd(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 0 < i < a.Length ==> result[i] == result[i-1] * a[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
