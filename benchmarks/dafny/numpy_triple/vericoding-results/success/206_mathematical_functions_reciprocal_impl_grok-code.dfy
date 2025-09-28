// <vc-preamble>
// Method that computes the element-wise reciprocal of a sequence
// Calculates 1/x for each element in the input sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed for this fix */
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
  /* code modified by LLM (iteration 5): Added loop invariants to enable Dafny verification of postconditions */
  var n := |x|;
  if n == 0 {
    result := [];
  } else {
    var res: seq<real> := [];
    var i: int := 0;
    while i < n 
      invariant 0 <= i <= n
      invariant |res| == i
      invariant forall k :: 0 <= k < i ==> res[k] == 1.0 / x[k]
    {
      res := res + [1.0 / x[i]];
      i := i + 1;
    }
    result := res;
  }
}
// </vc-code>
