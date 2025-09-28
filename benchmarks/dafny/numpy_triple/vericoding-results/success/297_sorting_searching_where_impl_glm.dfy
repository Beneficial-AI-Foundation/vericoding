// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SelectWhere(cond: bool, x: real, y: real): real {
  if cond then x else y
}
/* helper modified by LLM (iteration 3): fixed syntax errors in select function */
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
  /* code modified by LLM (iteration 3): fixed sequence comprehension syntax */
  result := seq(|condition|, i requires 0 <= i < |condition| => SelectWhere(condition[i], x[i], y[i]));
}
// </vc-code>
