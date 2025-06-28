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
            1 <= write_index <= read_index + 1,
            read_index <= nums.len(),
            write_index <= nums.len(),
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
            // Original array was sorted
            forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j]
    {
        if nums[read_index as int] != nums[write_index as int - 1] {
            // Move unique element to write position
            nums.set(write_index as int, nums[read_index as int]);
            
            // Prove that sorted order is maintained
            assert(write_index >= 1);
            assert(nums[write_index as int - 1] < nums[read_index as int]) by {
                assert(nums[write_index as int - 1] != nums[read_index as int]);
                assert(write_index as int - 1 < read_index);
                assert(forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j]);
            };
            
            write_index = write_index + 1;
        }
        
        read_index = read_index + 1;
    }

    // Final proof that all original elements are represented
    assert(read_index == nums.len());
    assert forall|k: int| 0 <= k < original_nums.len() implies 
        exists|i: int| 0 <= i < write_index && original_nums[k] == nums[i] by {
        // This follows from the loop invariant since we processed all elements
    };

    write_index
}

fn Testing() -> (result: (int, int, int, int))
{
    (0, 0, 0, 0)
}

}