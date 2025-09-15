// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added check for negative index */
function MatchesAt(s: string, sub: string, i: int): bool
{
  if |sub| == 0 then true
  else if i < 0 || i >= |s| then false
  else if |sub| > |s| - i then false
  else s[i] == sub[0] && MatchesAt(s, sub[1..], i+1)
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): unchanged from iteration 3 */
{
  var i := 0;
  while i <= |s| - |sub|
  {
    if MatchesAt(s, sub, i) {
      result := true;
      return;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
