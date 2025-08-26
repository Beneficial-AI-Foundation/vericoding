method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
// </vc-spec>
// <vc-code>
{
  mset := multiset{};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant mset == multiset(s[..i])
  {
    mset := mset + multiset{s[i]};
    i := i + 1;
    assert s[..i] == s[..i-1] + [s[i-1]];
    assert multiset(s[..i]) == multiset(s[..i-1]) + multiset{s[i-1]};
  }
}
// </vc-code>

// <vc-helpers>
// Helper lemmas if needed
// </vc-helpers>