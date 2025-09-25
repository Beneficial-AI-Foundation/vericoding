// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Square(arr: array<int>) returns (result: array<int>)
    ensures
        result.Length == arr.Length &&
        forall i :: 0 <= i < arr.Length ==> result[i] == arr[i] * arr[i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-code>
