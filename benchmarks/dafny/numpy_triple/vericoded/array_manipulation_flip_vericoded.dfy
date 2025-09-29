// <vc-preamble>
// Method that reverses the order of elements in a sequence
// Corresponds to numpy.flip for 1D arrays
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_flip(m: seq<real>) returns (result: seq<real>)
    // Size preservation: output has same length as input
    ensures |result| == |m|
    // Element mapping: element at position i in result equals 
    // element at position (n-1-i) in input
    ensures forall i :: 0 <= i < |m| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |m|
    invariant 0 <= i <= |m|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == m[|m| - 1 - j]
  {
    result := result + [m[|m| - 1 - i]];
    i := i + 1;
  }
}
// </vc-code>
