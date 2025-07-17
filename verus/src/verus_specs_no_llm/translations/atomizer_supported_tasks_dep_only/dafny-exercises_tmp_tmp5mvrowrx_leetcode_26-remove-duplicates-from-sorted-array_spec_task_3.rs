// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_RemoveDuplicates(nums: Vec<int>) -> num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..]
    requires
        forall i, j | 0 <= i < j < nums.len() :: nums.index(i) <= nums.index(j)
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall i, j | 0 <= i < j < num_length :: nums.index(i) != nums.index(j),
        forall i | 0 <= i < num_length :: nums.index(i) in old(nums.index(..)),
        forall i | 0 <= i < nums.len() :: old(nums.index(i)) in nums.index(..num_length)
;

proof fn lemma_RemoveDuplicates(nums: Vec<int>) -> (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length: : nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length: : nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
    requires
        forall i, j | 0 <= i < j < nums.len() :: nums.index(i) <= nums.index(j)
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall i, j | 0 <= i < j < num_length :: nums.index(i) != nums.index(j),
        forall i | 0 <= i < num_length :: nums.index(i) in old(nums.index(..)),
        forall i | 0 <= i < nums.len() :: old(nums.index(i)) in nums.index(..num_length)
{
    (0, 0, 0)
}

}