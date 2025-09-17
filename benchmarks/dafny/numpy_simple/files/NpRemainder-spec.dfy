// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method remainder(a: array<int>, b: array<int>) returns (result: array<int>)
    requires 
        a.Length == b.Length
    requires
        forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures
        result.Length == a.Length
    ensures
        forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-code>
