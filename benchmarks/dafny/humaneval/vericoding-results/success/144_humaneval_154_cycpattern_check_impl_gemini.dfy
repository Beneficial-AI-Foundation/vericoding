// <vc-preamble>
function IsSubstring(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}
function RotateString(s: string, n: nat): string
  requires 0 <= n <= |s|
{
  s[n..] + s[..n]
}
// </vc-preamble>

// <vc-helpers>
method FindRotatedSubstring(word: string, pattern: string, i: nat) returns (found: bool)
  requires 0 <= i <= |pattern| + 1
  ensures found <==> (exists k :: i <= k <= |pattern| && IsSubstring(word, RotateString(pattern, k)))
  decreases |pattern| + 1 - i
{
  if i > |pattern| {
    found := false;
  } else {
    if IsSubstring(word, RotateString(pattern, i)) {
      found := true;
    } else {
      found := FindRotatedSubstring(word, pattern, i + 1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)

  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
// </vc-spec>
// <vc-code>
{
  result := FindRotatedSubstring(word, pattern, 0);
}
// </vc-code>
