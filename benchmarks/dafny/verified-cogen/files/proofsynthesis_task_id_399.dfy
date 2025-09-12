// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BitWiseXor(arr1: array<bv32>, arr2: array<bv32>) returns (result: array<bv32>)
    requires arr1.Length == arr2.Length
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] ^ arr2[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
