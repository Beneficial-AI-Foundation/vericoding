function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma SumMonotonic(a: seq<int>, s: int, t1: int, t2: int)
  requires 0 <= s <= t1 <= t2 <= |a|
  requires forall i :: s <= i < t2 ==> a[i] >= 0
  ensures Sum(a, s, t1) <= Sum(a, s, t2)
{
  if t1 == t2 {
    // Base case: Sum(a, s, t1) == Sum(a, s, t2)
  } else {
    // Inductive case
    SumMonotonic(a, s, t1, t2-1);
    assert Sum(a, s, t2) == Sum(a, s, t2-1) + a[t2-1];
    assert a[t2-1] >= 0;
  }
}

lemma SumProperty(a: seq<int>, s: int, t: int, k: int)
  requires 0 <= s <= k <= t <= |a|
  ensures Sum(a, s, t) == Sum(a, s, k) + Sum(a, k, t)
{
  if k == t {
    // Base case
  } else {
    SumProperty(a, s, t-1, k);
    assert Sum(a, s, t) == Sum(a, s, t-1) + a[t-1];
    assert Sum(a, s, t-1) == Sum(a, s, k) + Sum(a, k, t-1);
    assert Sum(a, k, t) == Sum(a, k, t-1) + a[t-1];
  }
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
  ensures exists i, j :: 0 <= i <= j < |nums| && result == Sum(nums, i, j+1)
  ensures forall i, j :: 0 <= i <= j < |nums| ==> result <= Sum(nums, i, j+1)
// </vc-spec>
// <vc-code>
{
  result := nums[0];
  var currentSum := nums[0];
  
  for k := 1 to |nums|
    invariant result <= currentSum
    invariant exists i, j :: 0 <= i <= j < k && result == Sum(nums, i, j+1)
    invariant forall i, j :: 0 <= i <= j < k ==> result <= Sum(nums, i, j+1)
    invariant exists i :: 0 <= i < k && currentSum == Sum(nums, i, k)
  {
    if nums[k] < currentSum + nums[k] {
      currentSum := nums[k];
    } else {
      currentSum := currentSum + nums[k];
    }
    
    if currentSum < result {
      result := currentSum;
    }
  }
}
// </vc-code>
