pub fn twoSum(nums: &[i32], target: i32) -> (i: usize, j: usize)
    requires nums.len() > 1,
    requires exists|i: usize, j: usize| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures |result: (usize, usize)| {
        let (i, j) = result;
        0 <= i < j < nums.len() && nums[i] + nums[j] == target
    },
    ensures |result: (usize, usize)| {
        let (i, j) = result;
        forall|ii: usize, jj: usize| (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target
    },
    ensures |result: (usize, usize)| {
        let (i, j) = result;
        forall|jj: usize| i < jj < j ==> nums[i] + nums[jj] != target
    },
{
}