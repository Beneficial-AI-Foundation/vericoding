function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma SumProperties(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t <= |a|
  ensures Sum(a, s, s) == 0
  ensures s < t ==> Sum(a, s, t) == Sum(a, s, t-1) + a[t-1]
{
}

lemma SumSingleElement(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures Sum(a, i, i+1) == a[i]
{
}

lemma SumConcatenation(a: seq<int>, s: int, m: int, t: int)
  requires 0 <= s <= m <= t <= |a|
  ensures Sum(a, s, t) == Sum(a, s, m) + Sum(a, m, t)
{
  if m == t {
    assert Sum(a, m, t) == 0;
  } else {
    SumConcatenation(a, s, m, t-1);
    assert Sum(a, s, t) == Sum(a, s, t-1) + a[t-1];
    assert Sum(a, s, t-1) == Sum(a, s, m) + Sum(a, m, t-1);
  }
}

lemma SumExtend(a: seq<int>, s: int, t: int)
  requires 0 <= s < t < |a|
  ensures Sum(a, s, t+1) == Sum(a, s, t) + a[t]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def minSubArraySum(nums : list[int]) -> int
Given an array of integers nums, find the minimum sum of any non-empty sub-array of nums.
*/
// </vc-description>

// <vc-spec>
method minSubArraySum(nums: seq<int>) returns (result: int)
  requires |nums| > 0
  ensures exists i, j :: 0 <= i < j <= |nums| && Sum(nums, i, j) == result
  ensures forall i, j :: 0 <= i < j <= |nums| ==> Sum(nums, i, j) >= result
// </vc-spec>
// <vc-code>
method minSubArraySum(nums: seq<int>) returns (result: int)
  requires |nums| > 0
  ensures exists i, j :: 0 <= i < j <= |nums| && Sum(nums, i, j) == result
  ensures forall i, j :: 0 <= i < j <= |nums| ==> Sum(nums, i, j) >= result
{
  result := nums[0];
  SumSingleElement(nums, 0);
  
  var currentSum := 0;
  
  for k := 0 to |nums|
    invariant exists i, j :: 0 <= i < j <= |nums| && Sum(nums, i, j) == result
    invariant forall i, j :: 0 <= i < j <= k ==> Sum(nums, i, j) >= result
  {
    currentSum := 0;
    for j := k to |nums|
      invariant currentSum == Sum(nums, k, j)
      invariant exists i, jj :: 0 <= i < jj <= |nums| && Sum(nums, i, jj) == result
      invariant forall i, jj :: 0 <= i < jj <= k ==> Sum(nums, i, jj) >= result
      invariant forall jj :: k < jj <= j ==> Sum(nums, k, jj) >= result
    {
      currentSum := currentSum + nums[j];
      SumExtend(nums, k, j);
      if currentSum < result {
        result := currentSum;
      }
    }
  }
}
// </vc-code>
