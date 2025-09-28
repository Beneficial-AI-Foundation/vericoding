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
/* helper modified by LLM (iteration 5): Bitwise-AND is bounded by each operand for bv32 */
lemma AndLeLeftRight(a: bv32, b: bv32)
  ensures (a & b) <= a
  ensures (a & b) <= b
{
}

/* helper modified by LLM (iteration 5): Idempotence of bitwise AND for bv32 */
lemma AndIdempotent(a: bv32)
  ensures a & a == a
{
}

/* helper modified by LLM (iteration 5): Absorption of zero in bitwise AND for bv32 */
lemma AndZeroAbsorb(a: bv32)
  ensures a & 0 == 0
{
}
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
  /* code modified by LLM (iteration 5): iterative construction with invariants to satisfy postconditions */
  var n := |x1|;
  var res: seq<bv32> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == (x1[j] & x2[j])
    invariant forall j :: 0 <= j < i ==> res[j] <= x1[j] && res[j] <= x2[j]
  {
    res := res + [x1[i] & x2[i]];
    i := i + 1;
  }
  // Helpful assertions for specified algebraic properties on inputs
  assert forall k :: 0 <= k < n ==> x1[k] & 0 == 0;
  assert forall k :: 0 <= k < n ==> x1[k] & x1[k] == x1[k];
  assert forall k :: 0 <= k < n ==> (x1[k] & x2[k]) == (x2[k] & x1[k]);
  result := res;
}
// </vc-code>
