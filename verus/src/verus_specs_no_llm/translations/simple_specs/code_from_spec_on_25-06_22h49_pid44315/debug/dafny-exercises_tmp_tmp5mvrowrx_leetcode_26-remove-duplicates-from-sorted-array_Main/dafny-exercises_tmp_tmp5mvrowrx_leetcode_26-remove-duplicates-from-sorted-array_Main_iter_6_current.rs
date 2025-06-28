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
    ghost let original_nums = old(nums);
    
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
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] < nums[j],
            // First element unchanged
            nums[0] == original_nums[0],
            // Original array was sorted
            forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j],
            // Elements after write_index are from original (but may be outdated)
            forall|i: int| write_index <= i < nums.len() ==> exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k]
    {
        if nums[read_index as int] != nums[write_index as int - 1] {
            // Move unique element to write position
            nums.set(write_index as int, nums[read_index as int]);
            
            // Prove that the new element maintains sorted order
            assert(nums[write_index as int - 1] < nums[write_index as int]) by {
                // Since original array is sorted and we found a different element
                assert(nums[write_index as int - 1] != nums[read_index as int]);
                assert(write_index as int - 1 < read_index);
                // By transitivity and the fact that duplicates are adjacent in sorted array
                let prev_val = nums[write_index as int - 1];
                let curr_val = nums[read_index as int];
                assert(exists|k1: int, k2: int| 0 <= k1 < k2 < original_nums.len() 
                    && original_nums[k1] == prev_val && original_nums[k2] == curr_val);
                assert(prev_val <= curr_val);
                assert(prev_val != curr_val);
                assert(prev_val < curr_val);
            };
            
            write_index = write_index + 1;
        }
        
        read_index = read_index + 1;
    }

    // Final assertion to help with postcondition
    assert(read_index == nums.len());
    
    // Prove all original elements are represented
    assert forall|k: int| 0 <= k < original_nums.len() implies 
        exists|i: int| 0 <= i < write_index && original_nums[k] == nums[i] by {
        // From loop invariant: all elements up to read_index are represented
        // Since read_index == nums.len(), all elements are represented
        assert(read_index == original_nums.len());
    };

    // Prove distinctness with correct ordering
    assert forall|i: int, j: int| 0 <= i < j < write_index implies nums[i] != nums[j] by {
        // From loop invariant, we maintained strict ordering which implies distinctness
        if 0 <= i < j < write_index {
            assert(nums[i] < nums[j]);
            assert(nums[i] != nums[j]);
        }
    };

    write_index
}

fn Testing() -> (result: (int, int, int, int))
{
    (0, 0, 0, 0)
}

}