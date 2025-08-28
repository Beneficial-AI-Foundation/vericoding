// <vc-helpers>
// Helper function to check if a character is in a string
function ContainsChar(s: string, c: char): bool
{
  exists i :: 0 <= i < |s| && s[i] == c
}

// Lemma to help with proving properties about string concatenation
lemma ConcatPreservesContains(s1: string, s2: string, c: char)
  ensures ContainsChar(s1 + s2, c) == (ContainsChar(s1, c) || ContainsChar(s2, c))
{
  if ContainsChar(s1, c) {
    var i :| 0 <= i < |s1| && s1[i] == c;
    assert (s1 + s2)[i] == c;
  } else if ContainsChar(s2, c) {
    var i :| 0 <= i < |s2| && s2[i] == c;
    assert (s1 + s2)[|s1| + i] == c;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
// </vc-spec>
// </vc-spec>

// <vc-code>
method RemoveCharsImpl(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
  ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{
  v := "";
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant |v| <= i
    invariant forall k :: 0 <= k < |v| ==> (v[k] in s1) && !(v[k] in s2)
    invariant forall k :: 0 <= k < i ==> (s1[k] in s2) || (s1[k] in v)
  {
    if !ContainsChar(s2, s1[i]) {
      v := v + [s1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
