

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  if n <= 1 {
    result := true;
    return;
  }
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall k :: 0 <= k < i ==> s[k] == s[0]
  {
    if s[i] != s[0] {
      result := false;
      assert n > 1;
      assert s[0] != s[i];
      assert exists x, y :: 0 <= x < n && 0 <= y < n && x != y && s[x] != s[y];
      return;
    }
    i := i + 1;
  }
  // All characters up to index n-1 are equal to s[0]
  result := true;
  assert forall k :: 0 <= k < n ==> s[k] == s[0];
  assert forall i0, j0 :: 0 <= i0 < n && 0 <= j0 < n ==> s[i0] == s[j0];
  return;
}
// </vc-code>

