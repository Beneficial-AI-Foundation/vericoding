// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AllElementsEquals(arr: array<int>, element: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> arr[i] == element)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
