// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
