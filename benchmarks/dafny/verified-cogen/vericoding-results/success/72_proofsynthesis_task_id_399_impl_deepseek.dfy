// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function BV32Xor(a: bv32, b: bv32): bv32 { a ^ b }
/* helper modified by LLM (iteration 2): Added helper function for bitwise XOR operation */
// </vc-helpers>

// <vc-spec>
method BitWiseXor(arr1: array<bv32>, arr2: array<bv32>) returns (result: array<bv32>)
    requires arr1.Length == arr2.Length
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] ^ arr2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Simplified implementation with direct array initialization */
  var length := arr1.Length;
  result := new bv32[length];
  var i: int := 0;
  while i < length
    invariant 0 <= i <= length
    invariant forall j :: 0 <= j < i ==> result[j] == BV32Xor(arr1[j], arr2[j])
  {
    result[i] := BV32Xor(arr1[i], arr2[i]);
    i := i + 1;
  }
}
// </vc-code>
