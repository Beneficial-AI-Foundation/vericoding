// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BitwiseAnd(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == (a[i] & b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed index out of range error */
  result := seq(|a|, i requires 0 <= i < |a| => a[i] & b[i]);
}
// </vc-code>
