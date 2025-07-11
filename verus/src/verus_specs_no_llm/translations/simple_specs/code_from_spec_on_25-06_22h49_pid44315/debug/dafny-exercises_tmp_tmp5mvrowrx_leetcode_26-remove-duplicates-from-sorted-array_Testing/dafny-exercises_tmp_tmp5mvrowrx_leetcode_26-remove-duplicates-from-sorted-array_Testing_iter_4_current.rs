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
    let ghost original_nums = *nums;
    
    while read_index < nums.len()
        invariant
            1 <= write_index <= read_index <= nums.len(),
            nums.len() == original_nums.len(),
            // All elements before write_index are unique
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] != nums[j],
            // Elements in the unique part come from original array
            forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k],
            // Elements from read_index onwards are unchanged
            forall|i: int| read_index <= i < nums.len() ==> nums[i] == original_nums[i],
            // nums[0] is unchanged
            nums[0] == original_nums[0],
            // All processed elements are represented in the unique part
            forall|i: int| 0 <= i < read_index ==> exists|k: int| 0 <= k < write_index && original_nums[i] == nums[k],
            // The unique part preserves the sorted order
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] < nums[j],
            // The original array was sorted
            forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j],
            // Maintain connection to original precondition
            original_nums =~= old(nums),
            // Key invariant: unprocessed elements will find representation
            forall|i: int| read_index <= i < nums.len() ==> 
                (exists|k: int| 0 <= k < write_index && nums[i] == nums[k]) ||
                (forall|j: int| 0 <= j < write_index ==> nums[i] != nums[j])
    {
        if nums[read_index] != nums[write_index - 1] {
            // Prove that this new element is indeed unique
            assert(forall|k: int| 0 <= k < write_index ==> nums[read_index] != nums[k]) by {
                if exists|k: int| 0 <= k < write_index && nums[read_index] == nums[k] {
                    // Since array is sorted and nums[read_index] > nums[write_index-1]
                    // and all elements in [0..write_index) are sorted, this is impossible
                    assert(nums[read_index] > nums[write_index - 1]);
                    assert(forall|j: int| 0 <= j < write_index ==> nums[j] <= nums[write_index - 1]);
                    assert(false);
                }
            };
            
            nums.set(write_index, nums[read_index]);
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }
    
    // Establish that all original elements are represented
    assert(forall|i: int| 0 <= i < original_nums.len() ==> exists|k: int| 0 <= k < write_index && original_nums[i] == nums[k]) by {
        // This follows from the loop invariant since read_index == nums.len() now
        assert(read_index == nums.len());
        assert(original_nums.len() == nums.len());
        
        // The invariant tells us this is true for all processed elements
        assert(forall|i: int| 0 <= i < read_index ==> exists|k: int| 0 <= k < write_index && original_nums[i] == nums[k]);
        
        // Since read_index == nums.len() == original_nums.len(), we're done
    };
    
    // Final proof assertions to establish postconditions
    assert(forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] != nums[j]);
    
    assert(forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k]) by {
        assert(original_nums =~= old(nums));
    };
    
    assert(forall|i: int| 0 <= i < old(nums).len() ==> exists|k: int| 0 <= k < write_index && old(nums)[i] == nums[k]) by {
        assert(original_nums =~= old(nums));
    };
    
    write_index
}

}