// <vc-preamble>
// Method that computes the element-wise reciprocal of a sequence
// Calculates 1/x for each element in the input sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): implement reciprocal sequence via recursion avoiding comprehension syntax */
function reciprocal_seq(x: seq<real>): seq<real>
  requires forall i :: 0 <= i < |x| ==> x[i] != 0.0
  ensures |reciprocal_seq(x)| == |x|
  ensures forall i :: 0 <= i < |x| ==> reciprocal_seq(x)[i] == 1.0 / x[i]
  ensures forall i :: 0 <= i < |x| ==> reciprocal_seq(x)[i] != 0.0
  ensures forall i :: 0 <= i < |x| ==> (x[i] > 0.0 ==> reciprocal_seq(x)[i] > 0.0)
  ensures forall i :: 0 <= i < |x| ==> (x[i] < 0.0 ==> reciprocal_seq(x)[i] < 0.0)
  decreases |x|
{
  if |x| == 0 then []
  else [1.0 / x[0]] + reciprocal_seq(x[1..])
}
// </vc-helpers>

// <vc-spec>
method numpy_reciprocal(x: seq<real>) returns (result: seq<real>)
  // Precondition: All elements in x must be non-zero to avoid division by zero
  requires forall i :: 0 <= i < |x| ==> x[i] != 0.0
  // Postcondition: Result has same length as input
  ensures |result| == |x|
  // Postcondition: Each result element is the reciprocal of corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == 1.0 / x[i]
  // Postcondition: All result elements are non-zero (since input elements are non-zero)
  ensures forall i :: 0 <= i < |x| ==> result[i] != 0.0
  // Postcondition: Sign preservation - positive inputs yield positive outputs
  ensures forall i :: 0 <= i < |x| ==> (x[i] > 0.0 ==> result[i] > 0.0)
  // Postcondition: Sign preservation - negative inputs yield negative outputs
  ensures forall i :: 0 <= i < |x| ==> (x[i] < 0.0 ==> result[i] < 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use helper function to construct reciprocal sequence */
  result := reciprocal_seq(x);
}
// </vc-code>
