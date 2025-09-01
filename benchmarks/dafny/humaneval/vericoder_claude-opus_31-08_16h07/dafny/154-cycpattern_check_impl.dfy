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
lemma EmptyPatternLemma(word: string, pattern: string)
  requires |pattern| == 0
  ensures IsSubstring(word, RotateString(pattern, 0))
{
  assert pattern == "";
  assert RotateString(pattern, 0) == pattern[0..] + pattern[..0] == "" + "" == "";
  assert |word| >= 0;
  assert |word| >= |""|;
  if |word| == 0 {
    assert word[0..0] == "";
  } else {
    assert word[0..0] == "";
  }
  assert IsSubstring(word, "");
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
    EmptyPatternLemma(word, pattern);
    assert IsSubstring(word, RotateString(pattern, 0));
    return true;
  }
  
  var i := 0;
  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
  {
    var rotated := RotateString(pattern, i);
    if IsSubstring(word, rotated) {
      return true;
    }
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

