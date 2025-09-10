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
    // mn is rem[idx] and minimal among rem
    // update multisets: remove rem[idx] from rem and add to res
    // use lemma to justify multiset arithmetic if needed
    // perform the move
    res := res + [mn];
    // rem equals rem[..idx] + [mn] + rem[idx+1..] because mn == rem[idx]
    rem := rem[..idx] + rem[idx+1..];
    // After update, invariants should hold automatically (or by the helper lemma)
    // Provide a hint for the verifier about multiset equality
    if false {
      // dummy use of lemma to help the verifier in proofs (never executed)
      RemoveAtPreservesMultiset(rem + [mn], |rem + [mn]| - 1);
    }
  }
  sorted := res;
}
// </vc-code>

