use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(nums: &mut Vec<int>) -> (num_length: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
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

    // Ghost variable to track original array
    ghost let original_nums = *nums;
    
    let mut write_index: usize = 1;
    let mut read_index: usize = 1;

    while read_index < nums.len()
        invariant
            1 <= write_index <= read_index + 1 <= nums.len() + 1,
            nums.len() == original_nums.len(),
            // All elements in the result portion are distinct
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] != nums[j],
            // All elements in result come from original array
            forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k],
            // All processed original elements are represented in result
            forall|k: int| 0 <= k < read_index ==> exists|i: int| 0 <= i < write_index && original_nums[k] == nums[i],
            // Maintain sorted order in result portion
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] <= nums[j],
            // First element unchanged
            nums[0] == original_nums[0],
            // Read index bounds
            read_index <= nums.len(),
            // Original array was sorted
            forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j]
    {
        if nums[read_index] != nums[write_index - 1] {
            nums.set(write_index, nums[read_index]);
            
            // Prove that the new element comes from original array
            assert(exists|k: int| 0 <= k < original_nums.len() && nums[write_index] == original_nums[k]);
            
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }

    // Prove final postcondition about all original elements being represented
    assert(read_index == nums.len());
    
    // Prove the postcondition holds
    assert forall|k: int| 0 <= k < original_nums.len() implies 
        exists|i: int| 0 <= i < write_index && original_nums[k] == nums[i] by {
        // This follows from the loop invariant since read_index == nums.len()
        assert(k < read_index);
    };

    write_index
}

fn Testing() -> (result: (int, int, int, int))
{
    (0, 0, 0, 0)
}

}