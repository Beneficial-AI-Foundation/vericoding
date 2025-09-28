// <vc-preamble>
/*
 * Dafny specification for array copy functionality.
 * Provides a method to create a copy of a sequence with identical values
 * but independent memory representation.
 */

// Copy method that returns a sequence with identical values to the input
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Copy<T>(a: seq<T>) returns (result: seq<T>)
  // The result has the same length as the input
  ensures |result| == |a|
  // Every element in the result equals the corresponding element in the input
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): used an iterative approach to build the sequence for verifiability */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[j]
  {
    result := result + [a[i]];
    i := i + 1;
  }
}
// </vc-code>
