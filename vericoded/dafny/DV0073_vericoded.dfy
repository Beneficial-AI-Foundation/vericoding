// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function sumArray(nums: array<int>, i: int): int
  requires 0 <= i <= nums.Length
  reads nums
  decreases nums.Length - i
{
  if i == nums.Length then 0
  else nums[i] + sumArray(nums, i + 1)
}
// </vc-helpers>

// <vc-spec>
method solution(nums: array<int>) returns (result: int)
    requires
        1 <= nums.Length <= 100
    requires
        forall i :: 0 <= i < nums.Length ==> nums[i] >= 1 && nums[i] <= 100
    ensures
        result >= 0
// </vc-spec>
// <vc-code>
{
  var sum := 0;
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant sum == sumArray(nums, 0) - sumArray(nums, i)
    invariant sum >= 0
  {
    sum := sum + nums[i];
    i := i + 1;
  }
  result := sum;
}
// </vc-code>
