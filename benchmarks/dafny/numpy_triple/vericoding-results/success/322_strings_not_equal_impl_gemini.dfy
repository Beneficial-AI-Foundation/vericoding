// <vc-preamble>
// Element-wise string inequality comparison
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NotEqual(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
  // Input sequences must have the same length for element-wise comparison
  requires |x1| == |x2|
  
  // Output sequence has the same length as input sequences
  ensures |result| == |x1|
  
  // Each element of result is the inequality comparison of corresponding input elements
  ensures forall i :: 0 <= i < |x1| ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): replaced sequence constructor with a while loop to fix index out of range error */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |x1| == |x2|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == (x1[k] != x2[k])
  {
    result := result + [x1[i] != x2[i]];
    i := i + 1;
  }
}
// </vc-code>
