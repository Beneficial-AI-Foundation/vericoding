// <vc-preamble>
// Axiomatic definition of bitwise OR operation on integers
function {:axiom} {:extern} BitwiseOr(x: int, y: int): int

// Axiomatic properties of bitwise OR operation
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
lemma {:axiom} BitwiseOrZeroRight(x: int)
  ensures BitwiseOr(x, 0) == x

lemma {:axiom} BitwiseOrZeroLeft(x: int)
  ensures BitwiseOr(0, x) == x

lemma {:axiom} BitwiseOrNegOneRight(x: int)
  ensures BitwiseOr(x, -1) == -1

lemma {:axiom} BitwiseOrNegOneLeft(x: int)
  ensures BitwiseOr(-1, x) == -1

lemma {:axiom} BitwiseOrCommutative(x: int, y: int)
  ensures BitwiseOr(x, y) == BitwiseOr(y, x)

lemma {:axiom} BitwiseOrAssociative(x: int, y: int, z: int)
  ensures BitwiseOr(BitwiseOr(x, y), z) == BitwiseOr(x, BitwiseOr(y, z))

lemma {:axiom} BitwiseOrIdempotent(x: int)
  ensures BitwiseOr(x, x) == x

/**
 * Compute the bit-wise OR of two integer vectors element-wise.
 * Takes two sequences of integers of equal length and returns a sequence where each element
 * is the bitwise OR of the corresponding elements from the input sequences.
 */
method BitwiseOrVector(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
  requires |x1| == |x2|
  ensures |result| == |x1|
  // Basic element-wise operation property
  ensures forall i :: 0 <= i < |result| ==> result[i] == BitwiseOr(x1[i], x2[i])
  // Identity with zero vector (right): if x2[i] == 0, then result[i] == x1[i]
  ensures forall i :: 0 <= i < |result| && x2[i] == 0 ==> result[i] == x1[i]
  // Identity with zero vector (left): if x1[i] == 0, then result[i] == x2[i]
  ensures forall i :: 0 <= i < |result| && x1[i] == 0 ==> result[i] == x2[i]
  // Saturation with -1 (all bits set): if either input is -1, result is -1
  ensures forall i :: 0 <= i < |result| && (x1[i] == -1 || x2[i] == -1) ==> result[i] == -1
  // Commutativity: BitwiseOrVector(x1, x2) produces same result as BitwiseOrVector(x2, x1)
  ensures forall i :: 0 <= i < |result| ==> result[i] == BitwiseOr(x2[i], x1[i])
  // Idempotency: if vectors are equal, result equals the input
  ensures (forall i :: 0 <= i < |x1| ==> x1[i] == x2[i]) ==> 
          (forall i :: 0 <= i < |result| ==> result[i] == x1[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added comprehensive loop invariants for all postconditions */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == BitwiseOr(x1[j], x2[j])
    invariant forall j :: 0 <= j < i && x2[j] == 0 ==> result[j] == x1[j]
    invariant forall j :: 0 <= j < i && x1[j] == 0 ==> result[j] == x2[j]
    invariant forall j :: 0 <= j < i && (x1[j] == -1 || x2[j] == -1) ==> result[j] == -1
    invariant forall j :: 0 <= j < i ==> result[j] == BitwiseOr(x2[j], x1[j])
  {
    var orValue := BitwiseOr(x1[i], x2[i]);
    
    // Apply lemmas to help the verifier
    if x2[i] == 0 {
      BitwiseOrZeroRight(x1[i]);
    }
    if x1[i] == 0 {
      BitwiseOrZeroLeft(x2[i]);
    }
    if x1[i] == -1 {
      BitwiseOrNegOneLeft(x2[i]);
    }
    if x2[i] == -1 {
      BitwiseOrNegOneRight(x1[i]);
    }
    BitwiseOrCommutative(x1[i], x2[i]);
    
    result := result + [orValue];
    i := i + 1;
  }
  
  // Help prove idempotency postcondition
  if forall j :: 0 <= j < |x1| ==> x1[j] == x2[j] {
    assert forall j :: 0 <= j < |result| ==> result[j] == BitwiseOr(x1[j], x2[j]);
    forall j | 0 <= j < |result|
      ensures result[j] == x1[j]
    {
      BitwiseOrIdempotent(x1[j]);
      assert x1[j] == x2[j];
      assert BitwiseOr(x1[j], x2[j]) == BitwiseOr(x1[j], x1[j]);
      assert BitwiseOr(x1[j], x1[j]) == x1[j];
    }
  }
}
// </vc-code>
