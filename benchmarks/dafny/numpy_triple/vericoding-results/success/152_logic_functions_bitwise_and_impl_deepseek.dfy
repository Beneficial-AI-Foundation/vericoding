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
function AbsorbZero(a: bv32): bool { (a & 0) == 0 }
lemma Commutative(a: bv32, b: bv32) ensures (a & b) == (b & a) {}
lemma Idempotent(a: bv32) ensures (a & a) == a {}
lemma UpperBound(a: bv32, b: bv32) ensures (a & b) <= a && (a & b) <= b {}
lemma SequenceProperties(x1: seq<bv32>, x2: seq<bv32>, i: int)
  requires 0 <= i <= |x1|
  requires |x1| == |x2|
  ensures forall j :: 0 <= j < i ==> (x1[j] & x2[j]) <= x1[j] && (x1[j] & x2[j]) <= x2[j]
  ensures forall j :: 0 <= j < i ==> (x1[j] & 0) == 0
  ensures forall j :: 0 <= j < i ==> (x1[j] & x1[j]) == x1[j]
{}
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
  /* code modified by LLM (iteration 4): Fixed loop invariants with proper bounds */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] & x2[j])
    invariant forall j :: 0 <= j < i ==> result[j] <= x1[j] && result[j] <= x2[j]
    invariant forall j :: 0 <= j < i ==> (x1[j] & 0) == 0
    invariant forall j :: 0 <= j < i ==> (x1[j] & x1[j]) == x1[j]
  {
    result := result + [x1[i] & x2[i]];
    UpperBound(x1[i], x2[i]);
    i := i + 1;
    SequenceProperties(x1, x2, i);
  }
}
// </vc-code>
