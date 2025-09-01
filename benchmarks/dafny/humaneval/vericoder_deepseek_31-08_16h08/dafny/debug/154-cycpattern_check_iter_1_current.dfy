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
lemma LemmaSubstringRotate(s: string, sub: string, i: nat)
  requires 0 <= i <= |sub|
  ensures IsSubstring(s, RotateString(sub, i)) <==> IsSubstring(s, sub[i..] + sub[..i])
{
}

lemma LemmaRotateStringDefinition(sub: string, i: nat)
  requires 0 <= i <= |sub|
  ensures RotateString(sub, i) == sub[i..] + sub[..i]
{
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
  var n := |pattern|;
  if |pattern| == 0 {
    result := true;
    return;
  }
  
  result := false;
  var i: nat := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant !result ==> forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
    invariant result ==> exists j :: 0 <= j <= n && IsSubstring(word, RotateString(pattern, j))
  {
    var rotated := pattern[i..] + pattern[..i];
    if |word| >= |rotated| {
      var k: nat := 0;
      while k <= |word| - |rotated|
        invariant 0 <= k <= |word| - |rotated| + 1
        invariant !result ==> forall l :: 0 <= l < k ==> word[l..l+|rotated|] != rotated
        invariant result ==> exists l :: 0 <= l <= |word| - |rotated| && word[l..l+|rotated|] == rotated
      {
        if word[k..k+|rotated|] == rotated {
          result := true;
          break;
        }
        k := k + 1;
      }
    }
    if result {
      break;
    }
    i := i + 1;
  }
}
// </vc-code>

