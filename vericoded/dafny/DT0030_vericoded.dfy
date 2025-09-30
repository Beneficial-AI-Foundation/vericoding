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
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == one
  {
    result := result + [one];
    i := i + 1;
  }
}
// </vc-code>
