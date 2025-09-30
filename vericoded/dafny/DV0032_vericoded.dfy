// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove LIS is non-negative */
function LIS(nums: seq<int>, i: int): int
  requires 0 <= i <= |nums|
  ensures LIS(nums, i) >= 0
  decreases i
{
  if i == 0 then
    0
  else
    var prev := LIS(nums, i-1);
    var includeThis := 1 + LISEndingAt(nums, i-1, nums[i-1]);
    if includeThis > prev then includeThis else prev
}

function LISEndingAt(nums: seq<int>, i: int, maxVal: int): int
  requires 0 <= i <= |nums|
  ensures LISEndingAt(nums, i, maxVal) >= 0
  decreases i
{
  if i == 0 then
    0
  else if nums[i-1] < maxVal then
    var incl := 1 + LISEndingAt(nums, i-1, nums[i-1]);
    var excl := LISEndingAt(nums, i-1, maxVal);
    if incl > excl then incl else excl
  else
    LISEndingAt(nums, i-1, maxVal)
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures nums.Length == 0 ==> result == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Implementation using helper functions with non-negative guarantee */
{
  if nums.Length == 0 {
    result := 0;
  } else {
    result := LIS(nums[..], nums.Length);
  }
}
// </vc-code>
