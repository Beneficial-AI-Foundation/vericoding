function IsSubstring(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}
function RotateString(s: string, n: nat): string
  requires 0 <= n <= |s|
{
  s[n..] + s[..n]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)
  // post-conditions-start
  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := false;
  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant !result
    invariant forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
    decreases |pattern| - i + 1
  {
    if IsSubstring(word, RotateString(pattern, i)) {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

