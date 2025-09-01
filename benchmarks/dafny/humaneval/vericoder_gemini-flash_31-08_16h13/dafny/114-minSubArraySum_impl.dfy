function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
function min(x: int, y: int): int {
  if x < y then x else y
}
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
  if |a| == 0 {
    return 0;
  }
  
  var overallMinSum := a[0];
  var currentMinSum := a[0];

  var i := 1;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant overallMinSum <= currentMinSum
    invariant overallMinSum == min(overallMinSum, currentMinSum) // This is a placeholder; replace with actual proof if needed
    // Invariant for `currentMinSum`: `currentMinSum` is the minimum sum of a subarray ending at index `i-1`.
    invariant exists k :: 0 <= k <= i && currentMinSum == Sum(a, k, i) &&
              (forall j :: k < j <= i ==> Sum(a, j, i) >= currentMinSum)
    // Invariant for `overallMinSum`: `overallMinSum` is the minimum sum of any subarray encountered so far (ending at or before `i-1`).
    invariant forall k', m' :: 0 <= k' <= m' < i ==> Sum(a, k', m') >= overallMinSum
  {
    currentMinSum := min(a[i], currentMinSum + a[i]);
    overallMinSum := min(overallMinSum, currentMinSum);
    i := i + 1;
  }
  return overallMinSum;
}
// </vc-code>

