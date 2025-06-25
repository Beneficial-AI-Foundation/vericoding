pub fn twoSum(nums: &[int], target: int) -> (i: int, j: int)
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures |result: (int, int)|
        0 <= result.0 < result.1 < nums.len() && nums[result.0] + nums[result.1] == target,
    ensures |result: (int, int)|
        forall|ii: int, jj: int| (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
    ensures |result: (int, int)|
        forall|jj: int| result.0 < jj < result.1 ==> nums[result.0] + nums[jj] != target,
{
}