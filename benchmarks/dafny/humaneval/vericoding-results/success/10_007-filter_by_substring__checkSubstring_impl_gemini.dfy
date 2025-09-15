// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function checkSubstringRec(s: string, sub: string, i: int): bool
  requires |sub| > 0
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i + |sub| > |s| then
    false
  else if s[i..i+|sub|] == sub then
    true
  else
    checkSubstringRec(s, sub, i + 1)
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  if |sub| > |s| {
    result := false;
  } else if |sub| == 0 {
    result := true;
  } else {
    result := checkSubstringRec(s, sub, 0);
  }
}
// </vc-code>
