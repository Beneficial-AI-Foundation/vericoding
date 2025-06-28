use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(nums: &mut Vec<i32>) -> (num_length: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j]
    ensures 
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k],
        forall|i: int| 0 <= i < old(nums).len() ==> exists|k: int| 0 <= k < num_length && old(nums)[i] == nums[k]
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
            // All elements before write_index are unique
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] != nums[j],
            // Elements in the unique part come from original array
            forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k],
            // All original elements up to read_index are represented in the unique part
            forall|i: int| 0 <= i < read_index ==> exists|k: int| 0 <= k < write_index && old(nums)[i] == nums[k],
            // Preserved elements beyond write_index up to read_index
            forall|i: int| write_index <= i < read_index ==> nums[i] == old(nums)[i],
            // Elements from read_index onwards are unchanged
            forall|i: int| read_index <= i < nums.len() ==> nums[i] == old(nums)[i]
    {
        if nums[read_index] != nums[write_index - 1] {
            nums.set(write_index, nums[read_index]);
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }
    
    write_index
}

}