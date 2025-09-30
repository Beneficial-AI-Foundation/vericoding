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
lemma LenRotatePreserved(s: string, n: nat)
  requires 0 <= n <= |s|
  ensures |RotateString(s,n)| == |s|
{
  assert |RotateString(s,n)| == |s[n..] + s[..n]|;
  assert |s[n..] + s[..n]| == |s[n..]| + |s[..n]|;
  assert |s[n..]| == |s| - n;
  assert |s[..n]| == n;
  assert |s[n..]| + |s[..n]| == |s|;
}

// </vc-helpers>

// <vc-spec>
method CycpatternCheck(word: string, pattern: string) returns (result: bool)

  ensures result ==> exists i :: 0 <= i <= |pattern| && IsSubstring(word, RotateString(pattern, i))
  ensures !result ==> forall i :: 0 <= i <= |pattern| ==> !IsSubstring(word, RotateString(pattern, i))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var found := false;
  while i <= |pattern| && !found
    invariant 0 <= i <= |pattern| + 1
    invariant found ==> exists j :: 0 <= j < i && IsSubstring(word, RotateString(pattern, j))
    invariant !found ==> forall j :: 0 <= j < i ==> !IsSubstring(word, RotateString(pattern, j))
    decreases |pattern| + 1 - i
  {
    if IsSubstring(word, RotateString(pattern, i)) {
      found := true;
      i := |pattern| + 1;
    } else {
      i := i + 1;
    }
  }
  result := found;
}

// </vc-code>
