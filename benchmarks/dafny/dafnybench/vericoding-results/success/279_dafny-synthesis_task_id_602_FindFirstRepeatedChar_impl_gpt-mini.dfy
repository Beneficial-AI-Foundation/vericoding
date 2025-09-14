

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  found := false;
  c := if n > 0 then s[0] else ' ';
  var j := if n > 0 then 1 else 0;
  while j < n
    invariant 0 <= j <= n
    invariant forall k, l :: 0 <= k < l < j ==> s[k] != s[l]
  {
    var i := 0;
    var foundAt := -1;
    while i < j
      invariant 0 <= i <= j
      invariant (foundAt == -1) ==> (forall k :: 0 <= k < i ==> s[k] != s[j])
      invariant (foundAt != -1) ==> 0 <= foundAt < j && s[foundAt] == s[j]
    {
      if s[i] == s[j] {
        foundAt := i;
        i := j; // exit inner loop
      } else {
        i := i + 1;
      }
    }
    if foundAt != -1 {
      found := true;
      c := s[foundAt];
      return;
    }
    j := j + 1;
  }
  // no repeats found
  found := false;
  // c already assigned to some value above
}
// </vc-code>

