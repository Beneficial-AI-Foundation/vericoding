// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var bestK := 0;
  var bestM := 0;
  var t := 0;
  while t <= n
    invariant 0 <= t <= n
    invariant 0 <= bestK <= bestM <= t
    invariant forall p,q :: 0 <= p <= q < t ==> Sum(a, p, q) <= Sum(a, bestK, bestM)
    decreases n - t + 1
  {
    var s := 0;
    while s <= t
      invariant 0 <= s <= t + 1
      invariant 0 <= bestK <= bestM <= t
      invariant forall p,q :: 0 <= p <= q < t ==> Sum(a, p, q) <= Sum(a, bestK, bestM)
      invariant forall p :: 0 <= p < s ==> Sum(a, p, t) <= Sum(a, bestK, bestM)
      decreases t - s + 1
    {
      if Sum(a, s, t) > Sum(a, bestK, bestM) {
        bestK := s;
        bestM := t;
      }
      s := s + 1;
    }
    if t == n {
      assert forall p,q :: 0 <= p <= q <= t ==> Sum(a, p, q) <= Sum(a, bestK, bestM);
      k := bestK;
      m := bestM;
      return;
    }
    t := t + 1;
  }
}
// </vc-code>

