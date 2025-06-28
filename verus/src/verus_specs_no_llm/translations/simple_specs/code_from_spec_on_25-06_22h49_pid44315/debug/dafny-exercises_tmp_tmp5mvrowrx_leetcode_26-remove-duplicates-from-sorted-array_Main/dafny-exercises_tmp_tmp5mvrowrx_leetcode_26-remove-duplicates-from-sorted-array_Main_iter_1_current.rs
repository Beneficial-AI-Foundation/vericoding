use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(nums: &mut Vec<int>) -> (num_length: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j]
    ensures 
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k],
        forall|k: int| 0 <= k < old(nums).len() ==> exists|i: int| 0 <= i < num_length && old(nums)[k] == nums[i]
{
    if nums.len() == 0 {
        return 0;
    }

    let mut write_index: usize = 1;
    let mut read_index: usize = 1;

    while read_index < nums.len()
        invariant
            1 <= write_index <= read_index <= nums.len(),
            nums.len() == old(nums).len(),
            // All elements in the result portion are distinct
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] != nums[j],
            // All elements in result come from original array
            forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k],
            // All processed original elements are represented in result
            forall|k: int| 0 <= k < read_index ==> exists|i: int| 0 <= i < write_index && old(nums)[k] == nums[i],
            // Maintain sorted order in result portion
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] <= nums[j],
            // Elements beyond write_index maintain original values up to read_index processing
            forall|i: int| write_index <= i < nums.len() && i >= read_index ==> nums[i] == old(nums)[i]
    {
        if nums[read_index] != nums[write_index - 1] {
            nums.set(write_index, nums[read_index]);
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }

    write_index
}

fn Testing() -> (result: (int, int, int, int))
{
    (0, 0, 0, 0)
}

}