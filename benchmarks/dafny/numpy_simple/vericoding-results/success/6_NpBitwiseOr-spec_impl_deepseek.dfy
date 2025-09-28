// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Remove duplicate method definition */
// </vc-helpers>

// <vc-spec>
method BitwiseOr(a: array<bv32>, b: array<bv32>) returns (result: array<bv32>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == (a[i] | b[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Clear while loop implementation with proper invariants */
{
    result := new bv32[a.Length];
    var j := 0;
    while j < a.Length
        invariant j <= a.Length
        invariant forall k :: 0 <= k < j ==> result[k] == (a[k] | b[k])
    {
        result[j] := a[j] | b[j];
        j := j + 1;
    }
}
// </vc-code>
