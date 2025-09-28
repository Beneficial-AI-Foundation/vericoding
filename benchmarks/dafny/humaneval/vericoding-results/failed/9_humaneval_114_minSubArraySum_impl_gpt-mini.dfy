// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove Sum(a,p,p)==0 */
lemma Sum_zero(a: seq<int>, p: int)
  requires 0 <= p <= |a|
  ensures Sum(a,p,p) == 0
{
  // By definition of Sum, when s == t it is 0
  assert Sum(a,p,p) == 0;
}

/* helper modified by LLM (iteration 5): Sum increment lemma */
lemma Sum_inc(a: seq<int>, p: int, q: int)
  requires 0 <= p <= q < |a|
  ensures Sum(a,p,q+1) == Sum(a,p,q) + a[q]
  decreases q - p
{
  if p == q {
    // Sum(a,p,p+1) == Sum(a,p,p) + a[p]
    assert Sum(a,p,p) == 0;
    assert Sum(a,p,p+1) == 0 + a[p];
  } else {
    Sum_inc(a,p,q-1);
    assert Sum(a,p,q) == Sum(a,p,q-1) + a[q-1];
    assert Sum(a,p,q+1) == Sum(a,p,q) + a[q];
  }
}

// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)

  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): brute-force lexicographic enumeration with careful invariant maintenance */
  var n := |a|;
  // initialize s to an actual subarray sum so s == Sum(a,k,m) holds
  s := Sum(a,0,0);
  var k := 0;
  var m := 0;
  var p := 0;
  while p <= n
    decreases n + 1 - p
    invariant 0 <= p <= n+1
    invariant 0 <= k <= m <= n
    invariant s == Sum(a,k,m)
    invariant forall p0,q0 :: 0 <= p0 <= q0 < p ==> Sum(a,p0,q0) >= s
  {
    var q := p;
    while q <= n
      decreases n + 1 - q
      invariant p <= q <= n+1
      invariant 0 <= k <= m <= n
      invariant s == Sum(a,k,m)
      invariant forall p0,q0 :: 0 <= p0 <= q0 < p ==> Sum(a,p0,q0) >= s
      invariant forall q0 :: p <= q0 < q ==> Sum(a,p,q0) >= s
    {
      var cand := Sum(a,p,q);
      if cand < s {
        // capture old s and the relevant facts before updating s
        var old := s;
        assert forall p0,q0 :: 0 <= p0 <= q0 < p ==> Sum(a,p0,q0) >= old;
        assert forall q0 :: p <= q0 < q ==> Sum(a,p,q0) >= old;
        s := cand;
        k := p;
        m := q;
        // old > s (since cand < old)
        assert old > s;
        // from old facts and old > s we get the same facts for the new s
        assert forall p0,q0 :: 0 <= p0 <= q0 < p ==> Sum(a,p0,q0) >= s;
        assert forall q0 :: p <= q0 < q ==> Sum(a,p,q0) >= s;
      }
      // ensure the newly considered pair (p,q) satisfies the invariant after this step
      assert Sum(a,p,q) >= s;
      q := q + 1;
    }
    p := p + 1;
  }
  assert exists kk,mm :: 0 <= kk <= mm <= n && s == Sum(a,kk,mm);
  assert forall p,q :: 0 <= p <= q <= n ==> Sum(a,p,q) >= s;
}

// </vc-code>
