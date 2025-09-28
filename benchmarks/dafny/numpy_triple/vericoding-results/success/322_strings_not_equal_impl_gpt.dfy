// <vc-preamble>
// Element-wise string inequality comparison
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): boolean inequality function for strings */
function StringNotEqual(s1: string, s2: string): bool
{
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
{
  /* code modified by LLM (iteration 4): build result via loop with sequence concatenation and invariants */
  var n := |x1|;
  var r: seq<bool> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == (x1[j] != x2[j])
  {
    r := r + [StringNotEqual(x1[i], x2[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
