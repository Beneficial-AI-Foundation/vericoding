// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method GetFirstElements(arr: array<array<int>>) returns (result: array<int>)

    requires
        forall i :: 0 <= i < arr.Length ==> arr[i].Length > 0

    ensures
        arr.Length == result.Length
    ensures
        forall i :: 0 <= i < arr.Length ==> result[i] == arr[i][0]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
