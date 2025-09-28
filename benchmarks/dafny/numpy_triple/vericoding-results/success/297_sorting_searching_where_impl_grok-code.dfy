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
  /* code modified by LLM (iteration 3): Added loop invariants to prove postconditions */
  result := [];
  var i: int := 0;
  while i < |condition|
    invariant 0 <= i <= |condition|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> if condition[k] then result[k] == x[k] else result[k] == y[k]
  {
    if condition[i] {
      result := result + [x[i]];
    } else {
      result := result + [y[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
