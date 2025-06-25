// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn RemoveDuplicates(nums: Vec<int>) -> num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length: : nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length: : nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..]
    requires forall|i: int, j | 0 <= i < j < nums.len(): int| nums[i] <= nums[j]
    ensures nums.len() == old(nums).len(),
            0 <= num_length <= nums.len(),
            forall|i: int, j | 0 <= i < j < num_length: int| nums[i] != nums[j],
            forall|i | 0 <= i < num_length: int| nums[i] in old(nums[..]),
            forall|i | 0 <= i < nums.len(): int| old(nums[i]) in nums[..num_length]
{
}

}