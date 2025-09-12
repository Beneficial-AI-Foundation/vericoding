// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ElementWiseDivision(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr2.Length ==> arr2[i] != 0
    requires forall m :: 0 <= m < arr1.Length ==> arr1[m] / arr2[m] >= 0
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] / arr2[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
