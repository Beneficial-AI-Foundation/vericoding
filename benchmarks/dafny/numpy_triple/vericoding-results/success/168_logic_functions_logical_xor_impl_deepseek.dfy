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

method {:opaque} numpy_logical_xor_impl(x1: seq<bool>, x2: seq<bool>) returns (result: seq<bool>)
  requires |x1| == |x2|
  ensures |result| == |x1|
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] != x2[i])
{
  /* helper modified by LLM (iteration 2): fixed index bounds in invariants */
  result := [];
  var j := 0;
  while j < |x1|
    invariant 0 <= j <= |x1|
    invariant |result| == j
    invariant forall i :: 0 <= i < j ==> result[i] == (x1[i] != x2[i])
  {
    result := result + [x1[j] != x2[j]];
    j := j + 1;
  }
}

lemma numpy_logical_xor_commutative(x1: seq<bool>, x2: seq<bool>)
  requires |x1| == |x2|
  ensures numpy_logical_xor_pure(x1, x2) == numpy_logical_xor_pure(x2, x1)
{
  assert forall i :: 0 <= i < |x1| ==> (x1[i] != x2[i]) == (x2[i] != x1[i]);
}

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
  /* code modified by LLM (iteration 2): fixed index bounds in invariants and added proper termination */
  result := [];
  var index := 0;
  
  while index < |x1|
    invariant 0 <= index <= |x1|
    invariant |result| == index
    invariant forall i :: 0 <= i < index ==> result[i] == (x1[i] != x2[i])
  {
    result := result + [x1[index] != x2[index]];
    index := index + 1;
  }
  
  // Prove commutativity property
  numpy_logical_xor_commutative(x1, x2);
}
// </vc-code>
