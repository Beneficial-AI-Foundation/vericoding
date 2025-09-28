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
/* helper modified by LLM (iteration 2): simplified element-wise accessor for sums */
function addAt(x1: seq<real>, x2: seq<real>, i: int): real
  requires |x1| == |x2|
  requires 0 <= i < |x1|
{
  x1[i] + x2[i]
}

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
  /* code modified by LLM (iteration 2): implemented iterative construction of result with invariants */
  var r: seq<real> := [];
  var i: int := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == x1[j] + x2[j]
  {
    r := r + [x1[i] + x2[i]];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
