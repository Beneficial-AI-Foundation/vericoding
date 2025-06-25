pub fn twoSum(nums: &[i32], target: i32) -> (index1: usize, index2: usize)
    requires 
        2 <= nums.len(),
        exists|i: int, j: int| (0 <= i < j < nums.len() && nums[i as int] + nums[j as int] == target),
    ensures |result: (usize, usize)|
        result.0 != result.1 &&
        result.0 < nums.len() &&
        result.1 < nums.len() &&
        nums[result.0 as int] + nums[result.1 as int] == target,
{
}