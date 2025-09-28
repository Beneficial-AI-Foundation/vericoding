// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function dp(i: int, prev: int, nums: array<int>): int
  requires 0 <= i <= nums.Length
  requires -1 <= prev < i
  requires prev == -1 || 0 <= prev < nums.Length
  reads nums
  ensures 0 <= dp(i, prev, nums) <= nums.Length - i
  decreases nums.Length - i
{
  /* helper modified by LLM (iteration 4): Added postcondition to ensure dp result bounds */
  if i == nums.Length then 0
  else if prev == -1 || nums[i] > nums[prev] then
    max(dp(i+1, prev, nums), 1 + dp(i+1, i, nums))
  else
    dp(i+1, prev, nums)
}

function max(a: int, b: int): int
{
  if a > b then a else b
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= nums.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Added verification that dp result satisfies postconditions */
  if nums.Length == 0 {
    result := 0;
  } else {
    result := dp(0, -1, nums);
    assert result >= 0 && result <= nums.Length;
  }
}
// </vc-code>
