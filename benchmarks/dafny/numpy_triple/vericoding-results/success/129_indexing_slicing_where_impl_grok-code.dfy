// <vc-preamble>
// Type alias to represent floating point numbers (closest equivalent to Lean's Float)
type Float = real
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 2): added loop invariants to prove postconditions */
{
  var temp: seq<Float> := [];
  for i := 0 to |condition|
    invariant 0 <= i <= |condition|
    invariant |temp| == i
    invariant forall j :: 0 <= j < i ==> temp[j] == if condition[j] then x[j] else y[j]
  {
    if condition[i] {
      temp := temp + [x[i]];
    } else {
      temp := temp + [y[i]];
    }
  }
  result := temp;
}
// </vc-code>
