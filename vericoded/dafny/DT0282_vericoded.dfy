// <vc-preamble>
/*
 * Dafny specification for numpy.add: element-wise addition of two vectors.
 * Implements vector addition where each element of the result is the sum
 * of the corresponding elements from the input vectors.
 */

// Method that adds two vectors element-wise
// Corresponds to numpy.add functionality
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Add(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
    // Precondition: input vectors must have the same length
    requires |x1| == |x2|
    // Postcondition: result has same length as inputs
    ensures |result| == |x1|
    // Postcondition: each element is sum of corresponding input elements
    ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] + x2[i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x1[j] + x2[j]
  {
    result := result + [x1[i] + x2[i]];
    i := i + 1;
  }
}
// </vc-code>
