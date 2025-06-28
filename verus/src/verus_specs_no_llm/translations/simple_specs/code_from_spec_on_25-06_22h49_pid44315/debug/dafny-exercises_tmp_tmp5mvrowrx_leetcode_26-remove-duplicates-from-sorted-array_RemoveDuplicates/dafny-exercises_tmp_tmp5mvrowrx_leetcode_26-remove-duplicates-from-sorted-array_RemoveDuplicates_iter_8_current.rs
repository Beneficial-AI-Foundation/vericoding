use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(nums: &mut Vec<int>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums.spec_index(i) <= nums.spec_index(j)
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums.spec_index(i) != nums.spec_index(j),
        forall|i: int| 0 <= i < num_length ==> nums.spec_index(i) in old(nums)@,
        forall|i: int| 0 <= i < old(nums).len() ==> old(nums).spec_index(i) in nums@.subrange(0, num_length as int),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums.spec_index(i) < nums.spec_index(j)
    modifies nums
{
    if nums.len() == 0 {
        return 0;
    }

    let ghost orig_nums = nums@;
    let mut write_idx: usize = 1;
    let mut read_idx: usize = 1;
    
    while read_idx < nums.len()
        invariant
            nums.len() == orig_nums.len(),
            1 <= write_idx <= read_idx <= nums.len(),
            // Elements before write_idx are distinct
            forall|i: int, j: int| 0 <= i < j < write_idx ==> nums.spec_index(i) != nums.spec_index(j),
            // Elements before write_idx are sorted
            forall|i: int, j: int| 0 <= i < j < write_idx ==> nums.spec_index(i) < nums.spec_index(j),
            // Elements before write_idx come from original array
            forall|i: int| 0 <= i < write_idx ==> nums.spec_index(i) in orig_nums,
            // All original elements up to read_idx are represented in the first write_idx positions
            forall|k: int| 0 <= k < read_idx ==> orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int),
            // Preserved elements after write_idx
            forall|i: int| write_idx <= i < nums.len() ==> nums.spec_index(i) == orig_nums.spec_index(i),
            // First element is preserved
            nums.spec_index(0) == orig_nums.spec_index(0),
            // Original array was sorted
            forall|i: int, j: int| 0 <= i < j < orig_nums.len() ==> orig_nums.spec_index(i) <= orig_nums.spec_index(j),
    {
        if nums[read_idx] != nums[write_idx - 1] {
            // Proof that the new element maintains strict ordering
            proof {
                let ghost prev_val = nums.spec_index(write_idx - 1);
                let ghost curr_val = nums.spec_index(read_idx as int);
                
                // Current value equals original value at read_idx
                assert(curr_val == orig_nums.spec_index(read_idx as int));
                
                // Previous value exists in original array before read_idx
                assert(prev_val in orig_nums);
                
                // Find position of prev_val in original array
                assert(exists|j: int| 0 <= j < read_idx && orig_nums.spec_index(j) == prev_val) by {
                    // prev_val is in nums[0..write_idx) which contains all unique elements from orig_nums[0..read_idx)
                    assert(prev_val == nums.spec_index(write_idx - 1));
                    assert(0 <= write_idx - 1 < write_idx);
                    
                    // Since all elements in [0, read_idx) from orig_nums are represented in [0, write_idx)
                    // and prev_val is at position write_idx-1, it must come from some position < read_idx
                    let ghost temp_j = choose|j: int| 0 <= j < orig_nums.len() && orig_nums.spec_index(j) == prev_val;
                    
                    // We need to show this j is < read_idx
                    // If j >= read_idx, then orig_nums[j] hasn't been processed yet, contradiction
                    if temp_j >= read_idx {
                        // This would mean prev_val appears at position >= read_idx in original
                        // But prev_val is already in the processed unique elements [0, write_idx)
                        // This creates a contradiction with our invariant
                        assert(false);
                    }
                    assert(temp_j < read_idx);
                }
                
                let ghost j = choose|j: int| 0 <= j < read_idx && orig_nums.spec_index(j) == prev_val;
                assert(0 <= j < read_idx);
                assert(j < read_idx <= read_idx);
                assert(orig_nums.spec_index(j) == prev_val);
                
                // Since original array is sorted and j < read_idx
                assert(orig_nums.spec_index(j) <= orig_nums.spec_index(read_idx as int));
                assert(prev_val <= curr_val);
                
                // Since they are different and prev_val <= curr_val
                assert(prev_val != curr_val);
                assert(prev_val < curr_val);
            }
            
            nums.set(write_idx, nums[read_idx]);
            
            // Proof after assignment
            proof {
                // Verify that all invariants still hold after the assignment
                assert(forall|i: int| 0 <= i < write_idx + 1 ==> nums.spec_index(i) in orig_nums);
                assert(forall|k: int| 0 <= k <= read_idx ==> orig_nums.spec_index(k) in nums@.subrange(0, (write_idx + 1) as int));
                
                // Verify distinctness is maintained
                assert(forall|i: int, j: int| 0 <= i < j < write_idx + 1 ==> nums.spec_index(i) != nums.spec_index(j)) by {
                    if j == write_idx {
                        // New element is different from all previous elements
                        assert(nums.spec_index(j) != nums.spec_index(write_idx - 1));
                        // And by transitivity with strict ordering, different from all others
                    }
                }
                
                // Verify strict ordering is maintained
                assert(forall|i: int, j: int| 0 <= i < j < write_idx + 1 ==> nums.spec_index(i) < nums.spec_index(j));
            }
            
            write_idx += 1;
        }
        
        read_idx += 1;
    }
    
    // Final proof for postconditions
    proof {
        assert(forall|i: int| 0 <= i < orig_nums.len() ==> orig_nums.spec_index(i) in nums@.subrange(0, write_idx as int));
        assert(forall|i: int| 0 <= i < write_idx ==> nums.spec_index(i) in orig_nums);
        assert(forall|i: int, j: int| 0 <= i < j < write_idx ==> nums.spec_index(i) != nums.spec_index(j));
        assert(forall|i: int, j: int| 0 <= i < j < write_idx ==> nums.spec_index(i) < nums.spec_index(j));
    }
    
    write_idx
}

}