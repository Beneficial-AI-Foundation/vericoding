pub fn RemoveElement(nums: &mut [i32], val: i32) -> (newLength: usize)
    requires(true)
    ensures(|result: usize| 0 <= result <= nums.len())
    ensures(|result: usize| forall|i: usize| i < result ==> nums[i] != val)
    ensures(|result: usize| multiset(nums[..result]) == multiset(old(nums)[..]).remove(val))
{
}