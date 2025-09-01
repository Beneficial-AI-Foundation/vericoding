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
  s := 0;
  var p := 0;
  while p < |a| {
    invariant 0 <= p <= |a|
    invariant s == min { Sum(a, x, y) | 0 <= x < p && x <= y <= |a| }
    var q := p + 1;
    while q <= |a| {
      invariant p + 1 <= q <= |a| + 1
      invariant s == min { Sum(a, x, y) | 0 <= x < p && x <= y <= |a| || x == p && p <= y < q }
      var sum := Sum(a, p, q);
      if sum < s {
        s := sum;
      }
      q := q + 1;
    }
    p := p + 1;
  }
}
// </vc-code>

