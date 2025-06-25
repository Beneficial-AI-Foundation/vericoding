pub fn removeElement(nums: &mut [i32], val: i32) -> (i: usize)
    ensures(forall|k: usize| 0 < k < i < nums.len() ==> nums[k] != val)
{
}