// <vc-preamble>
/*
 * Dafny specification for numpy.bitwise_not operation.
 * Computes bit-wise inversion, or bit-wise NOT, element-wise on integer arrays.
 * In two's-complement representation, bitwise NOT of x equals -(x + 1).
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No change, helper is correct. */
function BitwiseNotOp(val: int): int { -(val + 1) }
// </vc-helpers>

// <vc-spec>
method BitwiseNot(x: seq<int>) returns (result: seq<int>)
  // No special preconditions required for bitwise NOT operation
  requires true
  
  // Result has same length as input
  ensures |result| == |x|
  
  // Each element in result is the bitwise NOT of corresponding input element
  // In two's-complement: ~x = -(x + 1)
  ensures forall i :: 0 <= i < |x| ==> result[i] == -(x[i] + 1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Replaced sequence constructor with an explicit while loop to resolve a compiler issue. */
  var i: nat := 0;
  result := [];
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == BitwiseNotOp(x[k])
  {
    result := result + [BitwiseNotOp(x[i])];
    i := i + 1;
  }
}
// </vc-code>
