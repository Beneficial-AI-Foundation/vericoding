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
lemma RotateStringLength(s: string, n: nat)
  requires 0 <= n <= |s|
  ensures |RotateString(s, n)| == |s|
{
}

lemma IsSubstringDecidable(word: string, rotated: string)
  ensures IsSubstring(word, rotated) || !IsSubstring(word, rotated)
{
}

lemma IsSubstringCorrectness(s: string, sub: string, i: int)
  requires 0 <= i <= |s| - |sub|
  requires |s| >= |sub|
  ensures s[i..i+|sub|] == sub <==> exists k {:trigger s[k..k+|sub|]} :: 0 <= k <= |s| - |sub| && s[k..k+|sub|] == sub
{
  if s[i..i+|sub|] == sub {
    assert s[i..i+|sub|] == sub;
  }
}

lemma EmptyPatternIsSubstring(word: string)
  ensures IsSubstring(word, "")
{
  if |word| >= 0 {
    assert word[0..0] == "";
    assert exists i :: 0 <= i <= |word| - 0 && word[i..i+0] == "";
  }
}

method FindSubstring(word: string, pattern: string) returns (found: bool)
  ensures found <==> IsSubstring(word, pattern)
{
  if |word| < |pattern| {
    return false;
  }
  
  if |pattern| == 0 {
    EmptyPatternIsSubstring(word);
    return true;
  }
  
  var i := 0;
  while i <= |word| - |pattern|
    invariant 0 <= i <= |word| - |pattern| + 1
    invariant forall j {:trigger word[j..j+|pattern|]} :: 0 <= j < i ==> word[j..j+|pattern|] != pattern
    invariant forall j :: 0 <= j < i ==> word[j..j+|pattern|] != pattern
  {
    if word[i..i+|pattern|] == pattern {
      assert word[i..i+|pattern|] == pattern;
      assert IsSubstring(word, pattern);
      return true;
    }
    i := i + 1;
  }
  
  assert forall j :: 0 <= j <= |word| - |pattern| ==> word[j..j+|pattern|] != pattern;
  assert !IsSubstring(word, pattern);
  return false;
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
  if |pattern| == 0 {
    assert exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i)) by {
      EmptyPatternIsSubstring(word);
      assert RotateString(pattern, 0) == "";
      assert IsSubstring(word, RotateString(pattern, 0));
    }
    return true;
  }
  
  var i := 0;
  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
  {
    var rotated := RotateString(pattern, i);
    var found := FindSubstring(word, rotated);
    if found {
      assert IsSubstring(word, rotated);
      assert IsSubstring(word, RotateString(pattern, i));
      assert exists k :: 0 <= k <= |pattern| && IsSubstring(word, RotateString(pattern, k));
      return true;
    }
    assert !IsSubstring(word, RotateString(pattern, i));
    i := i + 1;
  }
  
  assert forall j :: 0 <= j <= |pattern| ==> !IsSubstring(word, RotateString(pattern, j));
  return false;
}
// </vc-code>
