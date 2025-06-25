pub fn twoSum(nums: &[i32], target: i32) -> (index1: usize, index2: usize)
    requires
        2 <= nums.len(),
        exists|i: usize, j: usize| (0 <= i < j < nums.len() && nums[i] + nums[j] == target),
    ensures |result: (usize, usize)|
        result.0 != result.1 &&
        0 <= result.0 < nums.len() &&
        0 <= result.1 < nums.len() &&
        nums[result.0] + nums[result.1] == target,
{
}