// <vc-preamble>
// Method that reverses the order of elements in a sequence
// Corresponds to numpy.flip for 1D arrays
// </vc-preamble>

// <vc-helpers>

function ReverseSequence(m: seq<real>, n: nat): seq<real>
  requires n <= |m|
  ensures |ReverseSequence(m, n)| == n
  ensures forall i :: 0 <= i < n ==> ReverseSequence(m, n)[i] == m[n - 1 - i]
{
  if n == 0 then []
  else [m[n-1]] + ReverseSequence(m, n-1)
}

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
  result := ReverseSequence(m, |m|);
}
// </vc-code>
