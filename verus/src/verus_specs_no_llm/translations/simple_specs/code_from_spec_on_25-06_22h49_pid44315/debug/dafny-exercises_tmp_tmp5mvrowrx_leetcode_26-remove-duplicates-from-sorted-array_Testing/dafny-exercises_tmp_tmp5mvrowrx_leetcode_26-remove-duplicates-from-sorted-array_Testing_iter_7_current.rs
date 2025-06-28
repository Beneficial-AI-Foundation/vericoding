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
            1 <= write_index <= read_index + 1,
            read_index <= nums.len(),
            write_index <= nums.len(),
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
            // Additional invariant: elements beyond write_index up to read_index are unchanged from original
            forall|i: int| write_index <= i < read_index ==> nums[i] == original_nums[i],
    {
        if nums[read_index as int] != nums[(write_index - 1) as int] {
            // Move the unique element to write position
            nums.set(write_index, nums[read_index]);
            
            // Prove the new element maintains uniqueness
            assert(nums[read_index as int] > nums[(write_index - 1) as int]) by {
                // Since array is sorted and element is different, it must be greater
                assert(forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j]);
                assert(read_index > write_index - 1);
            };
            
            assert(forall|j: int| 0 <= j < write_index ==> nums[j] < nums[read_index as int]) by {
                let new_val = nums[read_index as int];
                assert(new_val > nums[(write_index - 1) as int]);
                assert(forall|k: int| 0 <= k < write_index - 1 ==> nums[k] < nums[(write_index - 1) as int]);
            };
            
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }
    
    // Final proof that all postconditions hold
    assert(forall|i: int| 0 <= i < original_nums.len() ==> 
        exists|k: int| 0 <= k < write_index && original_nums[i] == nums[k]) by {
        // From loop invariant: all processed elements (0..read_index) are represented
        // Since read_index == nums.len() == original_nums.len(), all elements are processed
        assert(read_index == nums.len());
        assert(nums.len() == original_nums.len());
    };
    
    assert(forall|i: int| 0 <= i < old(nums).len() ==> 
        exists|k: int| 0 <= k < write_index && old(nums)[i] == nums[k]) by {
        assert(original_nums =~= old(nums));
        assert(forall|i: int| 0 <= i < original_nums.len() ==> 
            exists|k: int| 0 <= k < write_index && original_nums[i] == nums[k]);
    };
    
    assert(forall|i: int| 0 <= i < write_index ==> 
        exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k]) by {
        assert(original_nums =~= old(nums));
        assert(forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k]);
    };
    
    write_index
}

}