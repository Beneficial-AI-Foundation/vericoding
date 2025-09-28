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
  var i := 0;
  var result_arr := new real[|condition|];

  while i < |condition|
    invariant 0 <= i <= |condition|
    invariant forall k :: 0 <= k < i ==> (if condition[k] then result_arr[k] == x[k] else result_arr[k] == y[k])
  {
    if condition[i] {
      result_arr[i] := x[i];
    } else {
      result_arr[i] := y[i];
    }
    i := i + 1;
  }

  result := result_arr[..];
}
// </vc-code>
