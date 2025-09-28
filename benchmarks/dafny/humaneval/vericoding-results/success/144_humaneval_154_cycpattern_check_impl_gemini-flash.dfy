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
function {:opaque} IsSubstringTransparent(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}
// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)

  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := false;
  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant !result ==> forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
  {
    if IsSubstring(word, RotateString(pattern, i))
    {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
