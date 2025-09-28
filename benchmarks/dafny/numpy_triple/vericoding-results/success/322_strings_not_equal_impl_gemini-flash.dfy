// <vc-preamble>
// Element-wise string inequality comparison
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed redundant `return` keyword, fixed compilation error by directly returning the boolean expression. */
function NotEqualSingle(s1: string, s2: string): bool {
  s1 != s2
}
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
/* code modified by LLM (iteration 2): Implemented method by iterating through input sequences and applying NotEqualSingle helper. */
{
  var i := 0;
  var res: seq<bool> := [];
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == (x1[k] != x2[k])
  {
    res := res + [NotEqualSingle(x1[i], x2[i])];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
