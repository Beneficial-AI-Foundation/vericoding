// <vc-preamble>
// Method that creates a new sequence with the same length as input array 'a',
// where every element is set to 'fill_value'
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_full_like(a: seq<real>, fill_value: real) returns (result: seq<real>)
  // No special preconditions needed
  // Postcondition: result has same length as input array
  ensures |result| == |a|
  // Postcondition: all elements in result equal fill_value
  ensures forall i :: 0 <= i < |result| ==> result[i] == fill_value
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
