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

// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)

  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant !result ==> forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
  {
    var rotated := RotateString(pattern, i);
    if IsSubstring(word, rotated) {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
