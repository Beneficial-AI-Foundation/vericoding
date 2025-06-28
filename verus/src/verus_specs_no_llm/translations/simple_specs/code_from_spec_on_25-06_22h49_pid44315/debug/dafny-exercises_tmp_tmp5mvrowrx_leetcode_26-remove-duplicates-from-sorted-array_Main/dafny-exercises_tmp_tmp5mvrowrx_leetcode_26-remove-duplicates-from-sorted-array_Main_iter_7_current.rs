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

    // Store original array in ghost variable
    proof {
        let ghost original_nums = *nums;
    }
    
    let mut write_index: usize = 1;
    let mut read_index: usize = 1;
    
    let ghost original_nums = *nums;

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
            forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j],
            // Elements after write_index preserve original elements
            forall|i: int| write_index <= i < nums.len() ==> exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k]
    {
        if nums[read_index] != nums[write_index - 1] {
            // Move unique element to write position
            nums.set(write_index, nums[read_index]);
            
            proof {
                // Establish that the new element maintains sorted order
                assert(nums[write_index - 1] <= nums[read_index]) by {
                    assert(write_index - 1 < read_index);
                    assert(exists|k1: int, k2: int| 0 <= k1 <= k2 < original_nums.len() 
                        && original_nums[k1] == nums[write_index - 1] && original_nums[k2] == nums[read_index]);
                };
                
                // Since they are different and sorted, strict inequality holds
                assert(nums[write_index - 1] < nums[write_index]) by {
                    assert(nums[write_index - 1] != nums[read_index]);
                    assert(nums[write_index - 1] <= nums[read_index]);
                    assert(nums[write_index] == nums[read_index]);
                };
            }
            
            write_index = write_index + 1;
        }
        
        read_index = read_index + 1;
    }

    proof {
        // Establish final postconditions
        assert(read_index == nums.len());
        assert(read_index == original_nums.len());
        
        // All original elements are represented
        assert forall|k: int| 0 <= k < original_nums.len() implies 
            exists|i: int| 0 <= i < write_index && original_nums[k] == nums[i] by {
            // From loop invariant with read_index == original_nums.len()
        };

        // Elements are distinct due to strict ordering
        assert forall|i: int, j: int| 0 <= i < j < write_index implies nums[i] != nums[j] by {
            if 0 <= i < j < write_index {
                assert(nums[i] <= nums[j]);
                // Need to prove strict inequality for distinctness
                if nums[i] == nums[j] {
                    // This would contradict our construction - we only add elements different from previous
                    assert(false);
                }
            }
        };
    }

    write_index
}

fn Testing() -> (result: (int, int, int, int))
{
    (0, 0, 0, 0)
}

}