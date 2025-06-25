pub fn two_sum(nums: &[i32], target: i32) -> (i32, i32)
    ensures(|r: (i32, i32)| 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
                                        nums[r.0 as usize] + nums[r.1 as usize] == target &&
                                        forall|i: usize, j: usize| 0 <= i < j < r.1 ==> nums[i] + nums[j] != target)
    ensures(|r: (i32, i32)| r.0 == -1 <==> forall|i: usize, j: usize| 0 <= i < j < nums.len() ==> nums[i] + nums[j] != target)
{
}