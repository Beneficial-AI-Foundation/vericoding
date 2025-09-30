// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NumpyWhere(condition: seq<bool>, x: seq<real>, y: seq<real>) returns (result: seq<real>)
  // All input sequences must have the same length
  requires |condition| == |x| == |y|
  
  // The result sequence has the same length as the input sequences
  ensures |result| == |condition|
  
  // For each index i, if condition[i] is true, result[i] equals x[i], 
  // otherwise result[i] equals y[i]
  ensures forall i :: 0 <= i < |result| ==> 
    if condition[i] then result[i] == x[i] else result[i] == y[i]
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |condition|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      if condition[j] then result[j] == x[j] else result[j] == y[j]
  {
    if condition[i] {
      result := result + [x[i]];
    } else {
      result := result + [y[i]];
    }
  }
}
// </vc-code>
