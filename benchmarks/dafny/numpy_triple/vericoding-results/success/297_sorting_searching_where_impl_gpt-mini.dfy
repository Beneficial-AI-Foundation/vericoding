// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): choose element based on boolean condition */
function Choose(cond: bool, a: real, b: real): real {
  if cond then a else b
}
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
  /* code modified by LLM (iteration 3): construct result by iteratively appending Choose(...) with invariants */
  var n := |condition|;
  var r: seq<real> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == Choose(condition[j], x[j], y[j])
  {
    r := r + [Choose(condition[i], x[i], y[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
