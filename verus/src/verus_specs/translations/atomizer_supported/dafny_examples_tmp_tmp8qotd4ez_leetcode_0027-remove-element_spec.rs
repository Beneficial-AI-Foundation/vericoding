pub fn RemoveElement(nums: &mut [i32], val: i32) -> (newLength: usize)
    requires(true)
    ensures(0 <= newLength <= nums.len())
    ensures(forall|x: i32| nums[..newLength].contains(x) ==> x != val)
    ensures(nums[..newLength].to_multiset() == old(nums).to_multiset().remove(val))
{
}