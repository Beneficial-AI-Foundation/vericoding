function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)
  // post-conditions-start
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  s := Sum(a, 0, 0);
  var bk := 0;
  var bm := 0;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant 0 <= bk <= bm < i
    invariant s == Sum(a, bk, bm)
    invariant forall p, q :: 0 <= p <= q < i ==> Sum(a, p, q) >= s
    decreases n - i + 1
  {
    var localMin := Sum(a, 0, i);
    var localK := 0;
    var j := 1;
    while j <= i
      invariant 1 <= j <= i + 1
      invariant 0 <= localK < j
      invariant localMin == Sum(a, localK, i)
      invariant forall p :: 0 <= p < j ==> Sum(a, p, i) >= localMin
      decreases i - j + 1
    {
      var sumji := Sum(a, j, i);
      if sumji < localMin {
        localMin := sumji;
        localK := j;
      }
      j := j + 1;
    }
    if localMin < s {
      s := localMin;
      bk := localK;
      bm := i;
    }
    assert forall p :: 0 <= p <= i ==> Sum(a, p, i) >= localMin;
    assert localMin >= s;
    assert forall p :: 0 <= p <= i ==> Sum(a, p, i) >= s;
    i := i + 1;
  }
  assert 0 <= bk <= bm <= n;
  assert s == Sum(a, bk, bm);
}
// </vc-code>

