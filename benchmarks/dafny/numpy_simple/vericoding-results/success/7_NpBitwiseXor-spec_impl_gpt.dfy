// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retained simple XOR wrapper for clarity */
function Xor32(x: bv32, y: bv32): bv32 { x ^ y }
// </vc-helpers>

// <vc-spec>
method BitwiseXor(a: array<bv32>, b: array<bv32>) returns (result: array<bv32>)
    requires 
        a.Length == b.Length &&
        a.Length > 0
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i] ^ b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement loop with proper invariants, removes null comparison, and uses direct XOR */
  result := new bv32[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] ^ b[j]
    decreases a.Length - i
  {
    result[i] := a[i] ^ b[i];
    i := i + 1;
  }
  assert i == a.Length;
  assert forall j :: 0 <= j < a.Length ==> result[j] == a[j] ^ b[j];
}
// </vc-code>
