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

lemma LemmaSubstringEquality(s: string, sub: string, i: nat)
  requires 0 <= i <= |s| - |sub|
  ensures s[i..i+|sub|] == sub ==> IsSubstring(s, sub)
{
}

lemma LemmaSubstringNotEqual(s: string, sub: string, i: nat)
  requires 0 <= i <= |s| - |sub|
  ensures s[i..i+|sub|] != sub ==> !(exists l {:trigger s[l..l+|sub|]} :: 0 <= l <= |s| - |sub| && s[l..l+|sub|] == sub)
{
}

lemma LemmaSubstringExists(s: string, sub: string)
  ensures IsSubstring(s, sub) <==> exists l {:trigger s[l..l+|sub|]} :: 0 <= l <= |s| - |sub| && s[l..l+|sub|] == sub
{
}

lemma LemmaRotateStringLength(sub: string, i: nat)
  requires 0 <= i <= |sub|
  ensures |RotateString(sub, i)| == |sub|
{
}

lemma LemmaSubstringTrigger(s: string, sub: string, l: nat)
  requires 0 <= l <= |s| - |sub|
  ensures s[l..l+|sub|] == sub ==> IsSubstring(s, sub)
{
}

lemma LemmaForallSubstring(s: string, sub: string, k: nat)
  requires 0 <= k <= |s| - |sub| + 1
  requires forall l {:trigger s[l..l+|sub|]} :: 0 <= l < k ==> s[l..l+|sub|] != sub
  ensures !(exists l :: 0 <= l < k && s[l..l+|sub|] == sub)
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
    invariant result ==> exists j :: 0 <= j < i && IsSubstring(word, RotateString(pattern, j))
  {
    var rotated := RotateString(pattern, i);
    LemmaRotateStringLength(pattern, i);
    if |word| >= |rotated| {
      var k: nat := 0;
      while k <= |word| - |rotated|
        invariant 0 <= k <= |word| - |rotated| + 1
        invariant !result ==> forall l {:trigger word[l..l+|rotated|]} :: 0 <= l < k ==> word[l..l+|rotated|] != rotated
        invariant !result ==> !(exists l :: 0 <= l < k && word[l..l+|rotated|] == rotated)
        invariant result ==> (exists l :: 0 <= l < k && word[l..l+|rotated|] == rotated)
      {
        LemmaForallSubstring(word, rotated, k);
        if word[k..k+|rotated|] == rotated {
          result := true;
        }
        if result {
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

