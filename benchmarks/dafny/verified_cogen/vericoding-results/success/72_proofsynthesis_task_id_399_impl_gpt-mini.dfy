// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [32-bit xor helper] */
function Xor32(a: bv32, b: bv32): bv32 { a ^ b }
// </vc-helpers>

// <vc-spec>
method BitWiseXor(arr1: array<bv32>, arr2: array<bv32>) returns (result: array<bv32>)
    requires arr1.Length == arr2.Length
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] ^ arr2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [implemented loop using helper] */
  result := new bv32[arr1.Length];
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant forall j :: 0 <= j < i ==> result[j] == Xor32(arr1[j], arr2[j])
    decreases arr1.Length - i
  {
    result[i] := Xor32(arr1[i], arr2[i]);
    i := i + 1;
  }
}
// </vc-code>
