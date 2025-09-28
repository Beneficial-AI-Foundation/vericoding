// <vc-preamble>
// Element-wise string inequality comparison
// </vc-preamble>

// <vc-helpers>
function NotEqualElement(x1: string, x2: string): bool { x1 != x2 }
/* helper modified by LLM (iteration 2): Element-wise string comparison helper */
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
  /* code modified by LLM (iteration 2): Fixed loop index boundaries */
  result := [];
  var index := 0;
  while index < |x1|
    invariant 0 <= index <= |x1|
    invariant |result| == index
    invariant forall j :: 0 <= j < index ==> result[j] == (x1[j] != x2[j])
  {
    result := result + [(x1[index] != x2[index])];
    index := index + 1;
  }
}
// </vc-code>
