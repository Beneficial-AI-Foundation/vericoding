function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
// </vc-helpers>
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
  s := 0;
  var n := |a|;

  for p in 0..n {
    var current := 0;
    var q := p;
    while q <= n {
      if current < s {
        s := current;
      }
      if q < n {
        current := current + a[q];
      }
      q := q + 1;
    }
  }
}
// </vc-code>

