pub fn remove_duplicates(nums: &mut [i32]) -> (num_length: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
    ensures 
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> old(nums)[i as int] == nums[i as int],
        forall|i: int| 0 <= i < nums.len() ==> exists|k: int| 0 <= k < num_length && old(nums)[i] == nums[k]
{
}