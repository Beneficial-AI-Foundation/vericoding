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
function IsSubstringHelper(s: string, sub: string, i: int): bool
  requires 0 <= i <= |s| - |sub|
{
  s[i..i+|sub|] == sub
}

lemma IsSubstringIff(s: string, sub: string)
  ensures |s| >= |sub| ==> (IsSubstring(s, sub) <==> exists i :: 0 <= i <= |s| - |sub| && IsSubstringHelper(s, sub, i))
{
  if |s| >= |sub| {
    calc {
      IsSubstring(s, sub);
    ==  { // def IsSubstring
      }
      exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub;
    ==  { // def IsSubstringHelper
      }
      exists i :: 0 <= i <= |s| - |sub| && IsSubstringHelper(s, sub, i);
    }
  }
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
  if |word| != |pattern| {
    return false;
  }
  if |pattern| == 0 {
    return true;
  }
  for i := 0 to |pattern| 
  {
    if IsSubstring(word, RotateString(pattern, i)) {
      return true;
    }
  }
  return false;
}
// </vc-code>

