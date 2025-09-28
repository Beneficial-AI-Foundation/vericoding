// <vc-preamble>
// Method that creates a sequence of ones with the same length as input
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method OnesLike<T>(a: seq<T>, one: T) returns (result: seq<T>)
  // Postcondition: result has same length as input
  ensures |result| == |a|
  // Postcondition: every element in result is the "one" value
  ensures forall i :: 0 <= i < |result| ==> result[i] == one
// </vc-spec>
// <vc-code>
{
  var r: seq<T> := [];
  while |r| < |a|
    invariant 0 <= |r| <= |a|
    invariant forall i :: 0 <= i < |r| ==> r[i] == one
    decreases |a| - |r|
  {
    r := r + [one];
  }
  result := r;
}
// </vc-code>
