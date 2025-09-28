// <vc-preamble>
// Type alias to represent floating point numbers (closest equivalent to Lean's Float)
type Float = real
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): executable recursive function constructing result sequence */
function WhereSeq(condition: seq<bool>, x: seq<Float>, y: seq<Float>): seq<Float>
  requires |condition| == |x| == |y|
  ensures |WhereSeq(condition, x, y)| == |condition|
  ensures forall i :: 0 <= i < |condition| ==> WhereSeq(condition, x, y)[i] == if condition[i] then x[i] else y[i]
  decreases |condition|
{
  if |condition| == 0 then []
  else [if condition[0] then x[0] else y[0]] + WhereSeq(condition[1..], x[1..], y[1..])
}
// </vc-helpers>

// <vc-spec>
method Where(condition: seq<bool>, x: seq<Float>, y: seq<Float>) returns (result: seq<Float>)
    // All input sequences must have the same length
    requires |condition| == |x| == |y|
    
    // The result sequence has the same length as the input sequences
    ensures |result| == |condition|
    
    // For each position i, result[i] is chosen from x[i] if condition[i] is true, 
    // otherwise from y[i]
    ensures forall i :: 0 <= i < |condition| ==> 
        result[i] == if condition[i] then x[i] else y[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): delegate to WhereSeq to construct result satisfying the specification */
  result := WhereSeq(condition, x, y);
}
// </vc-code>
