function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
function min(a: int, b: int): int {
  if a < b then a else b
}

// Function to calculate the sum of a subarray
function SubarraySum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else SubarraySum(a, s, t-1) + a[t-1]
}

// Function for the minimum sum ending at a given index
function MinSumEndingAt(a: seq<int>, idx: int): int
  requires 0 <= idx < |a|
  ensures exists k :: 0 <= k <= idx && MinSumEndingAt(a, idx) == SubarraySum(a, k, idx + 1)
  ensures forall k :: 0 <= k <= idx ==> SubarraySum(a, k, idx + 1) >= MinSumEndingAt(a, idx)
{
  if idx == 0 then a[0]
  else min(a[idx], a[idx] + MinSumEndingAt(a, idx - 1))
}

// Function for the overall minimum subarray sum up to a given index
function MinSubarraySum(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  ensures i == 0 ==> MinSubarraySum(a, i) == 0
  ensures 0 < i <= |a| ==> MinSubarraySum(a, i) == (min(MinSubarraySum(a, i - 1), MinSumEndingAt(a, i - 1)))
  ensures 0 < i <= |a| ==> (exists k, m :: 0 <= k <= m < i && MinSubarraySum(a, i) == SubarraySum(a, k, m))  // Adjusted postcondition
{
  if i == 0 then 0
  else if i == 1 then a[0]
  else min(MinSubarraySum(a, i - 1), MinSumEndingAt(a, i - 1))
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

  var currentMinEndingHere: int := a[0];
  var overallMin: int := a[0];

  var i: int := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant overallMin == MinSubarraySum(a, i)
    invariant currentMinEndingHere == MinSumEndingAt(a, i-1)
  {
    currentMinEndingHere := min(a[i], a[i] + currentMinEndingHere);
    overallMin := min(overallMin, currentMinEndingHere);
    i := i + 1;
  }
  return overallMin;
}
// </vc-code>

