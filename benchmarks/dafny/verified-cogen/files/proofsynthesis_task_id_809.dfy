// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsSmaller(arr1: array<int>, arr2: array<int>) returns (result: bool)
    requires arr1.Length == arr2.Length
    ensures result == (forall i :: 0 <= i < arr1.Length ==> arr1[i] > arr2[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
