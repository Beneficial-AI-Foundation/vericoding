// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helper functions needed */
// </vc-helpers>

// <vc-spec>
method MatchStrings(s: string, p: string) returns (result: bool)
    requires |s| == |p|
    ensures result == (forall n :: 0 <= n < |s| ==> 
        (s[n] == p[n] || p[n] == '?'))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed syntax error and implemented loop for string matching */
{
  var n := 0;
  result := true;
  while n < |s|
    invariant 0 <= n <= |s|
    invariant result == (forall i :: 0 <= i < n ==> (s[i] == p[i] || p[i] == '?'))
  {
    if s[n] == p[n] || p[n] == '?' {
      n := n + 1;
    } else {
      result := false;
      break;
    }
  }
}
// </vc-code>
