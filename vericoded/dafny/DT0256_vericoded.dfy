// <vc-preamble>
/*
 * Bitwise AND operations on sequences of natural numbers.
 * Implements element-wise bitwise AND operation similar to numpy.bitwise_and,
 * computing the bit-wise AND of the underlying binary representation of
 * natural numbers in input sequences.
 */

// Compute the bit-wise AND of two sequences element-wise
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BitwiseAnd(x1: seq<bv32>, x2: seq<bv32>) returns (result: seq<bv32>)
  // Input sequences must have the same length
  requires |x1| == |x2|
  // Result has the same length as input sequences
  ensures |result| == |x1|
  // Each element is the bitwise AND of corresponding input elements
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] & x2[i])
  // Commutativity property: a & b = b & a
  ensures forall i :: 0 <= i < |result| ==> (x1[i] & x2[i]) == (x2[i] & x1[i])
  // Absorption with zero: a & 0 = 0
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] & 0) == 0
  // Idempotent property: a & a = a
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] & x1[i]) == x1[i]
  // Result is bounded by both operands: result[i] <= x1[i] and result[i] <= x2[i]
  ensures forall i :: 0 <= i < |result| ==> result[i] <= x1[i] && result[i] <= x2[i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] & x2[j])
  {
    result := result + [x1[i] & x2[i]];
    i := i + 1;
  }
}
// </vc-code>
