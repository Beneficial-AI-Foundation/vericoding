function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
lemma RemoveAtPreservesMultiset<T>(s: seq<T>, idx: nat)
  requires 0 <= idx < |s|
  ensures multiset(s[..idx] + s[idx+1..]) + multiset([s[idx]]) == multiset(s)
{
  // s == s[..idx] + [s[idx]] + s[idx+1..]
  assert s == s[..idx] + [s[idx]] + s[idx+1..];
  // multiset of concatenation equals sum of multisets
  assert multiset(s) == multiset(s[..idx] + [s[idx]] + s[idx+1..]);
  assert multiset(s[..idx] + [s[idx]] + s[idx+1..]) == multiset(s[..idx]) + multiset([s[idx]]) + multiset(s[idx+1..]);
  assert multiset(s[..idx]) + multiset([s[idx]]) + multiset(s[idx+1..]) == multiset(s[..idx] + s[idx+1..]) + multiset([s[idx]]);
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var rem := s;
  var res: seq<nat> := [];
  // invariants: length and multiset partition, and res is sorted by popcount,
  // and last element of res (if any) is <= every element in rem by popcount
  while |rem| > 0
    invariant |res| + |rem| == |s|
    invariant multiset(res) + multiset(rem) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |res| ==> popcount(res[i]) <= popcount(res[j])
    invariant (|res| == 0) || (forall x :: 0 <= x < |rem| ==> popcount(res[|res|-1]) <= popcount(rem[x]))
  {
    // find index of minimal popcount in rem
    var idx := 0;
    var k := 1;
    var mn := rem[0];
    while k < |rem|
      invariant 0 <= idx < |rem|
      invariant 0 <= k <= |rem|
      invariant mn == rem[idx]
      invariant forall t :: 0 <= t < k ==> popcount(mn) <= popcount(rem[t])
    {
      if popcount(rem[k]) < popcount(mn) {
        mn := rem[k];
        idx := k;
      }
      k := k + 1;
    }
    // Capture old values before updating
    var oldRem := rem;
    var oldRes := res;
    // use lemma to justify multiset arithmetic
    // ensure lemma precondition
    assert 0 <= idx < |oldRem|;
    RemoveAtPreservesMultiset(oldRem, idx);
    // mn is the element at idx in oldRem
    assert mn == oldRem[idx];
    // build new sequences
    var newRes := oldRes + [mn];
    var newRem := oldRem[..idx] + oldRem[idx+1..];
    // show multisets update correctly
    assert multiset(newRes) == multiset(oldRes) + multiset([mn]);
    // from lemma: multiset(newRem) + multiset([oldRem[idx]]) == multiset(oldRem)
    assert multiset(newRem) + multiset([mn]) == multiset(oldRem);
    // combine with invariant multiset(oldRes) + multiset(oldRem) == multiset(s)
    assert multiset(oldRes) + multiset(oldRem) == multiset(s);
    // hence multiset(newRes) + multiset(newRem) == multiset(s)
    assert multiset(newRes) + multiset(newRem) == multiset(s);
    // perform the actual updates
    res := newRes;
    rem := newRem;
  }
  sorted := res;
}
// </vc-code>

