// <vc-preamble>
// Method that computes the element-wise reciprocal of a sequence
// Calculates 1/x for each element in the input sequence
// </vc-preamble>

// <vc-helpers>
function reciprocal_element(r: real): real
  requires r != 0.0
  ensures reciprocal_element(r) == 1.0 / r
{
  1.0 / r
}

lemma reciprocal_sign_preservation(r: real)
  requires r != 0.0
  ensures (r > 0.0 ==> 1.0 / r > 0.0) && (r < 0.0 ==> 1.0 / r < 0.0)
{
}

lemma reciprocal_nonzero(r: real)
  requires r != 0.0
  ensures 1.0 / r != 0.0
{
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
  /* code modified by LLM (iteration 4): Fixed bounds checking in invariants and added proper indexing */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == 1.0 / x[j]
    invariant forall j :: 0 <= j < i ==> result[j] != 0.0
    invariant forall j :: 0 <= j < i ==> (x[j] > 0.0 ==> result[j] > 0.0)
    invariant forall j :: 0 <= j < i ==> (x[j] < 0.0 ==> result[j] < 0.0)
  {
    result := result + [1.0 / x[i]];
    i := i + 1;
  }
}
// </vc-code>
