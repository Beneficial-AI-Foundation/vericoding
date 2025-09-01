function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
// Empty
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
  if |a| > 0 {
    var min_ending_here := a[0];
    var min_so_far := a[0];
    for i := 1 to |a|-1 {
      min_ending_here := if a[i] < min_ending_here + a[i] then a[i] else min_ending_here + a[i];
      if min_ending_here < min_so_far {
        min_so_far := min_ending_here;
      }
    }
    s := min_so_far;
    // Ensure empty subarray sum is considered
    if 0 < s {
      s := 0;
    }
  }
}
// </vc-code>

