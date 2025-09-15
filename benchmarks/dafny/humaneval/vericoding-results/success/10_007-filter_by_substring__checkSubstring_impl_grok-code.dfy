// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed trigger syntax by attaching it correctly to quantifier */
function IsSubstring(s: string, sub: string): bool
{
  exists k {:trigger s[k..k+|sub|]} :: 0 <= k <= |s| - |sub| && s[k..k+|sub|] == sub
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): simplified implementation using the IsSubstring helper function */
{
  return IsSubstring(s, sub);
}
// </vc-code>
