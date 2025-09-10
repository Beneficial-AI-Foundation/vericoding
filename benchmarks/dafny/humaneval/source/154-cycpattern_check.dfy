function IsSubstring(s: string, sub: string) : bool
{
  |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
}
// pure-end
function RotateString(s: string, n: nat): string
  requires 0 <= n <= |s|
{
  s[n..] + s[..n]
}
// pure-end
method CycpatternCheck(word: string, pattern: string) returns (result: bool)
  // post-conditions-start
  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
  // post-conditions-end
{
  // impl-start
  var i := 0;
  while i <= |pattern|
    // invariants-start
    invariant 0 <= i <= |pattern| + 1
    invariant forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
    // invariants-end
  {
    if IsSubstring(word, RotateString(pattern, i)) {
      return true;
    }
    i := i + 1;
  }
  return false;
  // impl-end
}
