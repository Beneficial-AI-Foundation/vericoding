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
function method RotateAndCheck(word: string, pattern: string, i: nat): bool
  requires 0 <= i <= |pattern|
{
  IsSubstring(word, RotateString(pattern, i))
}
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
  var found := false;
  var i := 0;
  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant found ==> exists k :: 0 <= k < i && IsSubstring(word, RotateString(pattern, k))
    invariant !found ==> forall k :: 0 <= k < i ==> !IsSubstring(word, RotateString(pattern, k))
  {
    if IsSubstring(word, RotateString(pattern, i))
    {
      found := true;
      break;
    }
    i := i + 1;
  }
  return found;
}
// </vc-code>

