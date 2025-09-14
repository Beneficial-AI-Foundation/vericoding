

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  if |s| <= 1 {
    result := true;
    return;
  }
  var c := s[0];
  var i := 1;
  result := true;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant result ==> forall k:int :: 0 <= k < i ==> s[k] == c
    decreases |s| - i
  {
    if s[i] != c {
      result := false;
      assert 1 <= i < |s|;
      assert |s| > 1;
      assert s[0] == c;
      assert s[i] != s[0];
      assert i != 0;
      assert exists ii:int, jj:int :: ii == 0 && jj == i &&
                             0 <= ii < |s| && 0 <= jj < |s| &&
                             ii != jj && s[ii] != s[jj];
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

