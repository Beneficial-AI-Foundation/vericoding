// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma MaxSumEmptyProperty(a: seq<int>, p: int, q: int)
  requires 0 <= p <= q <= |a|
  ensures (q == p) ==> (Sum(a, p, q) == 0)
{
}
// </vc-helpers>

// <vc-spec>
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var currentMaxSum := 0;
  var overallMaxSum := 0;
  var currentStart := 0;
  var overallStart := 0;
  var overallEnd := 0;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= currentStart <= i
    invariant 0 <= overallStart <= overallEnd <= i
    invariant overallMaxSum == Sum(a, overallStart, overallEnd)
    invariant forall p,q :: 0 <= p <= q <= i ==> Sum(a, p, q) <= overallMaxSum
    invariant currentMaxSum == Sum(a, currentStart, i)
    invariant forall p,q :: 0 <= p <= q <= i && q == i ==> Sum(a, p, q) <= currentMaxSum
  {
    var sumWithCurrent := currentMaxSum + a[i];
    if sumWithCurrent > 0 {
      currentMaxSum := sumWithCurrent;
    } else {
      currentMaxSum := 0;
      currentStart := i + 1;
    }

    if currentMaxSum > overallMaxSum {
      overallMaxSum := currentMaxSum;
      overallStart := currentStart;
      overallEnd := i + 1;
    }
    i := i + 1;
  }
  k := overallStart;
  m := overallEnd;
}
// </vc-code>

