// <vc-preamble>
// Type alias to represent floating point numbers (closest equivalent to Lean's Float)
type Float = real
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma asserting input sequences have equal lengths using non-chained equality */
lemma TripleLengthsEqual(condition: seq<bool>, x: seq<Float>, y: seq<Float>)
  requires |condition| == |x| && |x| == |y|
{
  // Precondition already states the equality of lengths; no further proof needed.
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
  /* code modified by LLM (iteration 3): build result by allocating an array and filling elements based on condition */
  var n := |condition|;
  var a := new Float[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == (if condition[j] then x[j] else y[j])
  {
    if condition[i] {
      a[i] := x[i];
    } else {
      a[i] := y[i];
    }
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
