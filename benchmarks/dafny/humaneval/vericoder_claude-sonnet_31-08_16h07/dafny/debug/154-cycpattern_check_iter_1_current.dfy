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

lemma IsSubstringDecidable(s: string, sub: string) returns (found: bool)
  ensures found <==> IsSubstring(s, sub)
{
  if |s| < |sub| {
    found := false;
    return;
  }
  
  found := false;
  var i := 0;
  while i <= |s| - |sub|
    invariant 0 <= i <= |s| - |sub| + 1
    invariant !found ==> forall j :: 0 <= j < i ==> s[j..j+|sub|] != sub
    invariant found ==> exists j :: 0 <= j < i && s[j..j+|sub|] == sub
  {
    if s[i..i+|sub|] == sub {
      found := true;
      return;
    }
    i := i + 1;
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
  if |pattern| == 0 {
    result := IsSubstring(word, "");
    return;
  }
  
  var i := 0;
  while i <= |pattern|
    invariant 0 <= i <= |pattern| + 1
    invariant forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
  {
    RotateStringLength(pattern, i);
    var rotated := RotateString(pattern, i);
    var found := IsSubstringDecidable(word, rotated);
    if found {
      result := true;
      return;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>

