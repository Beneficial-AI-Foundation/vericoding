// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  var j := 0;
  found := false;
  c := 'a'; // default value

  while j < |s|
    invariant 0 <= j <= |s|
    invariant !found ==> (forall k, l :: 0 <= k < l < j ==> s[k] != s[l])
  {
    var i := 0;
    while i < j
      invariant 0 <= i <= j
      invariant j < |s|
      invariant !found ==> (forall k, l :: 0 <= k < l < j ==> s[k] != s[l])
      invariant forall k :: 0 <= k < i ==> s[k] != s[j]
    {
      if s[i] == s[j] {
        found := true;
        c := s[j];
        return;
      }
      i := i + 1;
    }
    j := j + 1;
  }
}
// </vc-code>
