// <vc-preamble>
// Method to concatenate two sequences of real numbers
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Concatenate(a: seq<real>, b: seq<real>) returns (result: seq<real>)
  // Postcondition: result has length equal to sum of input lengths
  ensures |result| == |a| + |b|
  
  // Postcondition: first |a| elements of result match vector a
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
  
  // Postcondition: next |b| elements of result match vector b  
  ensures forall j :: 0 <= j < |b| ==> result[|a| + j] == b[j]
// </vc-spec>
// <vc-code>
{
  result := a + b;
}
// </vc-code>
