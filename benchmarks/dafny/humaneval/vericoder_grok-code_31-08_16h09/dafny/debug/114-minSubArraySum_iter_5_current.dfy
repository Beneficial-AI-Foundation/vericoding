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
  var min_ending_here := 0;
  var min_so_far := 0;
  if |a| > 0 {
    min_ending_here := a[0];
    min_so_far := if min_ending_here < min_so_far then min_ending_here else min_so_far;
    for i := 1 to |a|-1 {
      min_ending_here := if a[i] < min_ending_here + a[i] then a[i] else min_ending_here + a[i];
      if min_ending_here < min_so_far {
        min_so_far := min_ending_here;
      }
    }
  }
  s := min_so_far;
}
// </vc-code>

