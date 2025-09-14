

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  var m: map<char,int> := map[];
  var j := 0;
  found := false;
  c := 'a';
  while j < |s|
    invariant 0 <= j <= |s|
    invariant forall k:int, l:int :: 0 <= k < l < j ==> s[k] != s[l]
    invariant forall t: char :: t in m ==> 0 <= m[t] < j && s[m[t]] == t
    invariant forall idx:int :: 0 <= idx < j ==> s[idx] in m
    decreases |s| - j
  {
    if s[j] in m {
      found := true;
      c := s[j];
      assert c in m;
      assert 0 <= m[c] < j && s[m[c]] == c;
      return;
    } else {
      m := m[s[j] := j];
      j := j + 1;
    }
  }
  return;
}
// </vc-code>

