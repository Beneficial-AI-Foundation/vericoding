

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  var seen: set<char> := {};
  var i: nat := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in seen <==> exists p :: 0 <= p < i && s[p] == x
    invariant forall k, l :: 0 <= k < l < i ==> s[k] != s[l]
  {
    if s[i] in seen {
      found := true;
      c := s[i];
      return;
    }
    seen := seen + {s[i]};
    i := i + 1;
  }
  found := false;
  c := ' ';
}
// </vc-code>

