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
lemma RotationIsSubstring(s: string, rotation: string, target: string)
  requires rotation in set r | r in RotationsOf(s)
  requires IsSubstring(target, rotation)
  ensures exists r :: r in RotationsOf(s) && IsSubstring(target, r)
{
}

function RotationsOf(s: string): set<string>
{
  set n | 0 <= n <= |s| :: RotateString(s, n)
}

lemma RotationsComplete(s: string)
  ensures forall n :: 0 <= n <= |s| ==> RotateString(s, n) in RotationsOf(s)
{
}

lemma IsSubstringEquivalence(s: string, sub: string)
  ensures IsSubstring(s, sub) <==> (|s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub)
{
  if IsSubstring(s, sub) {
    assert |s| >= |sub|;
    assert exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub;
  }
  if |s| >= |sub| && exists i {:trigger s[i..i+|sub|]} :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub {
    assert IsSubstring(s, sub);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def cycpattern_check(String a, String b) -> Bool
You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word, else False
*/
// </vc-description>

// <vc-spec>
method CycpatternCheck(a: string, b: string) returns (result: bool)
  ensures result <==> exists n :: 0 <= n <= |b| && IsSubstring(a, RotateString(b, n))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i <= |b|
    invariant 0 <= i <= |b| + 1
    invariant forall n :: 0 <= n < i ==> !IsSubstring(a, RotateString(b, n))
  {
    var rotation := RotateString(b, i);
    if |a| >= |rotation| && |rotation| > 0 {
      var j := 0;
      while j <= |a| - |rotation|
        invariant 0 <= j <= |a| - |rotation| + 1
        invariant forall k {:trigger a[k..k+|rotation|]} :: 0 <= k < j ==> a[k..k+|rotation|] != rotation
        invariant |rotation| > 0
      {
        if a[j..j+|rotation|] == rotation {
          assert IsSubstring(a, rotation);
          assert rotation == RotateString(b, i);
          return true;
        }
        j := j + 1;
      }
      if |rotation| > 0 {
        assert forall k {:trigger a[k..k+|rotation|]} :: 0 <= k <= |a| - |rotation| ==> a[k..k+|rotation|] != rotation;
        assert !IsSubstring(a, rotation);
      }
    }
    if |rotation| == 0 {
      assert !IsSubstring(a, rotation) || |a| == 0;
      if |a| == 0 {
        assert IsSubstring(a, rotation);
        return true;
      }
    }
    if |a| < |rotation| {
      assert !IsSubstring(a, rotation);
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
