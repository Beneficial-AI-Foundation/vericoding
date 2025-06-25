pub fn remove_duplicates(nums: &mut [i32]) -> (num_length: usize)
    requires
        forall|i: usize, j: usize| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: usize, j: usize| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: usize| 0 <= i < num_length ==> old(nums)[i as int] == nums[i],
        forall|i: usize| 0 <= i < nums.len() ==> exists|k: usize| 0 <= k < num_length && old(nums)[i as int] == nums[k]
{
}

pub fn testing()
{
}