pub fn remove_element(nums: &mut [i32], val: i32) -> (i: usize)
    requires
        0 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= nums[i] <= 50,
        0 <= val <= 100,
    ensures
        forall|j: int| 0 < j < i < nums.len() ==> nums[j] != val,
{
}