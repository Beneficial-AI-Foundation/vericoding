// <vc-preamble>
/*
 * Dafny specification for numpy.bitwise_not operation.
 * Computes bit-wise inversion, or bit-wise NOT, element-wise on integer arrays.
 * In two's-complement representation, bitwise NOT of x equals -(x + 1).
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): compute bitwise not for an integer */
function BitwiseNotInt(x: int): int { -(x + 1) }
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
  /* code modified by LLM (iteration 2): build result sequence element-wise */
  var res: seq<int> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == -(x[j] + 1)
  {
    res := res + [BitwiseNotInt(x[i])];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
