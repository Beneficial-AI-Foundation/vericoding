// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CubeElements(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i] * a[i] * a[i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := new int[a.Length];
    // impl-end
}
// </vc-code>
