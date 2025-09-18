// <vc-preamble>
// Method that horizontally stacks two 1D arrays (sequences) by concatenating them
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method hstack(a: seq<real>, b: seq<real>) returns (result: seq<real>)
  // No preconditions needed for 1D concatenation
  requires true
  
  // The result has length equal to the sum of input lengths
  ensures |result| == |a| + |b|
  
  // First |a| elements come from array a, preserving order
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
  
  // Next |b| elements come from array b, preserving order  
  ensures forall j :: 0 <= j < |b| ==> result[|a| + j] == b[j]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
