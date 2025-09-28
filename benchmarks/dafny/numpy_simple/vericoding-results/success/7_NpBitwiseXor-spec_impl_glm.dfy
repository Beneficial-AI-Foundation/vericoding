// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): using forall assignment to avoid timeout */
  result := new bv32[a.Length];
  forall i | 0 <= i < a.Length {
    result[i] := a[i] ^ b[i];
  }
}
// </vc-code>
