// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires
        nums.Length > 1 &&
        exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
    ensures
        0 <= result.0 < result.1 < nums.Length &&
        nums[result.0] + nums[result.1] == target
// </vc-spec>
// <vc-code>
{
  var i, j :| 0 <= i < j < nums.Length && nums[i] + nums[j] == target;
  result := (i, j);
}
// </vc-code>
