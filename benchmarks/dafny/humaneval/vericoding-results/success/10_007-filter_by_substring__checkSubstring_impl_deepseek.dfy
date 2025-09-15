// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function StringContains(s: string, sub: string, start: int): bool 
  requires 0 <= start <= |s|
  decreases |s| - start
{
  if start + |sub| > |s| then false
  else if s[start..start+|sub|] == sub then true
  else StringContains(s, sub, start + 1)
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  if |sub| == 0 {
    result := true;
  } else {
    result := StringContains(s, sub, 0);
  }
}
// </vc-code>
