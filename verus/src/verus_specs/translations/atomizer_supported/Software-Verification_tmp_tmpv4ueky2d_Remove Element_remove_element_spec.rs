pub fn remove_element(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    requires(0 <= nums.len() <= 100)
    requires(forall|i: usize| 0 <= i < nums.len() ==> 0 <= nums[i] <= 50)
    requires(0 <= val <= 100)
    ensures(forall|j: usize| 0 < j < i < nums.len() ==> nums[j] != val)
{
}