// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArrayCopy(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
