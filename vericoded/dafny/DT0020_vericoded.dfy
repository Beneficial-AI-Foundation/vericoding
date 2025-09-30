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
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == fill_value
  {
    result := result + [fill_value];
    i := i + 1;
  }
}
// </vc-code>
