// <vc-preamble>
/**
 * Computes the logical NOT of each element in the input sequence according to NumPy semantics.
 * Uses NumPy's truthiness convention: zero is falsy (NOT zero = true), 
 * all non-zero values are truthy (NOT non-zero = false).
 */
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LogicalNot(x: seq<real>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed index out of range error by ensuring valid sequence construction */
  result := seq(|x|, i requires 0 <= i < |x| => x[i] == 0.0);
}
// </vc-code>
