function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

function min(a: int, b: int): int {
  if a < b then a else b
}

function MinSum(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  // Ensures that MinSum(a, i) is the minimum sum of any subarray ending at or before index i.
  ensures forall p, q :: 0 <= p <= q <= i && q > 0 ==> Sum(a, p, q) >= MinSum(a, i)
  // Ensures that MinSum(a, i) is one of the sums of a subarray ending at or before index i.
  ensures exists k, m :: 0 <= k <= m <= i && m > 0 && MinSum(a, i) == Sum(a, k, m)
  // Ensures that if i > 0, MinSum(a, i) is either MinSum(a, i-1) or some sum ending at i.
  ensures i == 0 ==> MinSum(a, i) == 0
  ensures i > 0 ==> MinSum(a, i) == min(MinSum(a, i-1), SumEndingAt(a, i))
{
  if i == 0 then 0
  else if i == 1 then a[0]
  else min(MinSum(a, i-1), SumEndingAt(a, i))
}

function SumEndingAt(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  ensures forall p :: 0 <= p < i ==> Sum(a, p, i) >= SumEndingAt(a, i)
  ensures exists k :: 0 <= k < i && SumEndingAt(a, i) == Sum(a, k, i)
{
  if i == 0 then 0
  else if i == 1 then a[0]
  else min(a[i-1], a[i-1] + SumEndingAt(a, i-1))
}

function MinSumEndingAt(a: seq<int>, idx: int): int
  requires 0 <= idx < |a|
  ensures exists k :: 0 <= k <= idx && MinSumEndingAt(a, idx) == Sum(a, k, idx + 1)
  ensures forall k :: 0 <= k <= idx ==> Sum(a, k, idx + 1) >= MinSumEndingAt(a, idx)
{
  if idx == 0 then a[0]
  else min(a[idx], a[idx] + MinSumEndingAt(a, idx - 1))
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

  var currentMinEndingHere: int := 0; // Represents the minimum sum of a subarray ending at the current index.
  var overallMin: int := 0; // Represents the minimum sum found so far in the entire array.

  // Initialize overallMin with the first element, as single-element subarrays are valid.
  overallMin := a[0];
  currentMinEndingHere := a[0];

  var i: int := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant overallMin <= currentMinEndingHere
    invariant forall p, q :: 0 <= p <= q < i ==> Sum(a, p, q) >= overallMin
    invariant exists k, m :: 0 <= k <= m < i && overallMin == Sum(a, k, m)
    invariant forall p, q :: 0 <= p <= q < i ==> (q-p == 0 ==> Sum(a, p, q) == 0)
    invariant currentMinEndingHere == MinSumEndingAt(a, i-1)
    invariant overallMin == MinSum(a, i-1)
  {
    // The current element a[i] can either start a new subarray or extend the previous one.
    // We want the minimum sum of a subarray ending at index i.
    // This is either a[i] itself or a[i] + the minimum sum of a subarray ending at i-1.
    currentMinEndingHere := min(a[i], a[i] + currentMinEndingHere);
    overallMin := min(overallMin, currentMinEndingHere);
    i := i + 1;
  }
  return overallMin;
}
// </vc-code>

