// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(arr: array<int>, elem: int) returns (result: array<int>)
    ensures
        result.Length == (2 * arr.Length) &&
        (forall k :: 0 <= k < arr.Length ==> result[2 * k] == elem) &&
        (forall k :: 0 <= k < arr.Length ==> result[2 * k + 1] == arr[k])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
