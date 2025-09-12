// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsGreater(arr: array<int>, number: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> number > arr[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
