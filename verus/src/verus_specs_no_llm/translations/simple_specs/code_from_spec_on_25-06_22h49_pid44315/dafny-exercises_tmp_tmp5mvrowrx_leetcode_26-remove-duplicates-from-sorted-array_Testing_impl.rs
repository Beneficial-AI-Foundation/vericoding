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
            original_nums == old(nums),
            // All elements before write_index are unique
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] != nums[j],
            // Elements in the unique part come from original array
            forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k],
            // Elements from read_index onwards are unchanged
            forall|i: int| read_index <= i < nums.len() ==> nums[i] == original_nums[i],
            // nums[0] is unchanged
            nums[0] == original_nums[0],
            // The unique part preserves the sorted order
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] < nums[j],
            // The original array was sorted
            forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j],
            // Key invariant: every distinct value in original[0..read_index] appears in nums[0..write_index]
            forall|val: i32| (exists|i: int| 0 <= i < read_index && original_nums[i] == val) ==>
                (exists|j: int| 0 <= j < write_index && nums[j] == val),
    {
        if nums[read_index as int] != nums[(write_index - 1) as int] {
            // Move the unique element to write position
            nums[write_index] = nums[read_index];
            
            proof {
                // Prove that the new element maintains uniqueness
                assert(forall|i: int| 0 <= i < write_index ==> nums[i] != nums[write_index as int]) by {
                    assert(forall|i: int| 0 <= i < write_index ==> {
                        if i == write_index - 1 {
                            assert(nums[i] != nums[read_index as int]);
                            true
                        } else {
                            assert(nums[i] < nums[write_index - 1]);
                            assert(nums[write_index - 1] < nums[read_index as int]);
                            assert(nums[i] < nums[read_index as int]);
                            true
                        }
                    });
                };
                
                // Prove that the new element comes from the original array
                assert(exists|k: int| 0 <= k < original_nums.len() && nums[write_index] == original_nums[k]);
                
                // Prove sorted order is maintained
                assert(forall|i: int, j: int| 0 <= i < j < write_index + 1 ==> nums[i] < nums[j]);
            }
            
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }
    
    // Final proof that all postconditions hold
    proof {
        // At this point, read_index == nums.len(), so we've processed all elements
        assert(read_index == nums.len());
        assert(nums.len() == original_nums.len());
        assert(original_nums == old(nums));
        
        // From the key invariant: every distinct value in original[0..read_index] appears in nums[0..write_index]
        // Since read_index == original_nums.len(), this covers all original values
        assert(forall|val: i32| (exists|i: int| 0 <= i < original_nums.len() && original_nums[i] == val) ==>
            (exists|j: int| 0 <= j < write_index && nums[j] == val));
        
        // This implies the postcondition about original elements appearing in result
        assert(forall|i: int| 0 <= i < old(nums).len() ==> 
            exists|k: int| 0 <= k < write_index && old(nums)[i] == nums[k]) by {
            assert(forall|i: int| 0 <= i < old(nums).len() ==> {
                let val = old(nums)[i];
                assert(original_nums[i] == val);
                assert(exists|j: int| 0 <= j < original_nums.len() && original_nums[j] == val);
                assert(exists|k: int| 0 <= k < write_index && nums[k] == val);
                true
            });
        };
        
        // Prove the other direction: elements in result come from original
        assert(forall|i: int| 0 <= i < write_index ==> 
            exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k]) by {
            assert(forall|i: int| 0 <= i < write_index ==> {
                assert(exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k]);
                assert(exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k]);
                true
            });
        };
    }
    
    write_index
}

}