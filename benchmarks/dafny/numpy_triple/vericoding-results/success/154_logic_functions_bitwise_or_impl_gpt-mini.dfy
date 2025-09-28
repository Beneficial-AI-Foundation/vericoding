// <vc-preamble>
/*
 * Dafny specification for numpy.bitwise_or: Compute the bit-wise OR of two arrays element-wise.
 * 
 * Computes the bit-wise OR of the underlying binary representation of the integers in the input arrays.
 * For integer inputs, the result is the bitwise OR of the binary representations.
 */

// Axiomatic definition of bitwise OR operation for integers
function BitwiseOr(x: int, y: int): int
{
    // Placeholder implementation for compilation
    0
}

// Axioms for bitwise OR properties
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): SeqOfArrayLength returns length of array slice */
lemma SeqOfArrayLength(a: array<int>)
  ensures |a[..]| == a.Length
{
}

/* helper modified by LLM (iteration 3): ArraySliceElement relates slice indexing to array indexing */
lemma ArraySliceElement(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures a[..][i] == a[i]
{
}

// </vc-helpers>

// <vc-spec>
lemma {:axiom} BitwiseOrCommutative(x: int, y: int)
    ensures BitwiseOr(x, y) == BitwiseOr(y, x)

lemma {:axiom} BitwiseOrIdentity(x: int)
    ensures BitwiseOr(x, 0) == x

lemma {:axiom} BitwiseOrIdempotent(x: int)
    ensures BitwiseOr(x, x) == x

// Main method for numpy bitwise_or operation
method NumpyBitwiseOr(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
    // Precondition: input sequences must have the same length
    requires |x1| == |x2|
    // Postcondition: result has same length as inputs
    ensures |result| == |x1|
    // Postcondition: each element is bitwise OR of corresponding input elements
    ensures forall i :: 0 <= i < |result| ==> result[i] == BitwiseOr(x1[i], x2[i])
    // Mathematical properties hold for all elements
    ensures forall i :: 0 <= i < |result| ==> BitwiseOr(x1[i], x2[i]) == BitwiseOr(x2[i], x1[i])
    ensures forall i :: 0 <= i < |x1| ==> BitwiseOr(x1[i], 0) == x1[i]
    ensures forall i :: 0 <= i < |x1| ==> BitwiseOr(x1[i], x1[i]) == x1[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build result array and invoke axiomatic lemmas per element to satisfy postconditions */
  var arr := new int[|x1|];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant forall j :: 0 <= j < i ==> arr[j] == BitwiseOr(x1[j], x2[j])
  {
    arr[i] := BitwiseOr(x1[i], x2[i]);
    i := i + 1;
  }
  result := arr[..];

  var k := 0;
  while k < |x1|
    invariant 0 <= k <= |x1|
    invariant forall j :: 0 <= j < k ==> BitwiseOr(x1[j], 0) == x1[j] && BitwiseOr(x1[j], x1[j]) == x1[j] && BitwiseOr(x1[j], x2[j]) == BitwiseOr(x2[j], x1[j])
  {
    BitwiseOrIdentity(x1[k]);
    BitwiseOrIdempotent(x1[k]);
    BitwiseOrCommutative(x1[k], x2[k]);
    k := k + 1;
  }
}

// </vc-code>
