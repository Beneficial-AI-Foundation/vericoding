// <vc-preamble>
// Ghost function to support commutativity property in specification
ghost function numpy_logical_xor_pure(x1: seq<bool>, x2: seq<bool>): seq<bool>
  requires |x1| == |x2|
  ensures |numpy_logical_xor_pure(x1, x2)| == |x1|
  ensures forall i :: 0 <= i < |x1| ==> numpy_logical_xor_pure(x1, x2)[i] == (x1[i] != x2[i])
{
  seq(|x1|, i requires 0 <= i < |x1| => x1[i] != x2[i])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_logical_xor(x1: seq<bool>, x2: seq<bool>) returns (result: seq<bool>)
  // Precondition: input sequences must have the same length
  requires |x1| == |x2|
  
  // Postconditions: result has same length and each element is XOR of corresponding inputs
  ensures |result| == |x1|
  ensures |result| == |x2|
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] != x2[i])
  
  // Additional properties: commutativity
  ensures result == numpy_logical_xor_pure(x2, x1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented with loop to avoid index out of range in seq comprehension */
  var n := |x1|;
  result := [];
  for i := 0 to n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] != x2[j])
  {
    result := result + [(x1[i] != x2[i])];
  }
}
// </vc-code>
