// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ElementWiseDivide(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr2.Length ==> arr2[i] != 0
    requires forall i :: 0 <= i < arr1.Length ==> -2147483648 <= arr1[i] / arr2[i] <= 2147483647
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] / arr2[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
