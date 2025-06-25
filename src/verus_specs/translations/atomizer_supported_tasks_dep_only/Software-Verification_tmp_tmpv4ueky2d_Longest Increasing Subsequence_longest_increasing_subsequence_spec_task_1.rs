pub fn longest_increasing_subsequence(nums: &[i32]) -> (max: i32)
    requires(1 <= nums.len() <= 2500)
    requires(forall|i: usize| 0 <= i < nums.len() ==> -10000 <= nums[i] <= 10000)
    ensures(|max: i32| max >= 1)
{
}

pub fn find_max(x: i32, y: i32) -> (result: i32)
{
    if x > y { x } else { y }
}