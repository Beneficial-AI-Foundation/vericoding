use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(nums: &mut Vec<int>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums).spec_index(i) <= old(nums).spec_index(j)
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums.spec_index(i) != nums.spec_index(j),
        forall|i: int| 0 <= i < num_length ==> nums.spec_index(i) in old(nums)@,
        forall|i: int| 0 <= i < old(nums).len() ==> old(nums).spec_index(i) in nums@.subrange(0, num_length as int),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums.spec_index(i) < nums.spec_index(j)
{
    if nums.len() == 0 {
        return 0;
    }

    let ghost orig_nums = old(nums)@;
    let mut write_idx: usize = 1;
    let mut read_idx: usize = 1;
    
    while read_idx < nums.len()
        invariant
            nums.len() == old(nums).len(),
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
    {
        if nums[read_idx] != nums[write_idx - 1] {
            nums.set(write_idx, nums[read_idx]);
            
            proof {
                // Prove that the new element maintains distinctness
                assert forall|i: int| 0 <= i < write_idx implies nums.spec_index(i) != nums.spec_index(write_idx as int) by {
                    // The new element at write_idx is nums[read_idx]
                    // All elements before write_idx are < nums[write_idx-1] 
                    // And nums[read_idx] > nums[write_idx-1]
                    if i < write_idx {
                        if i == write_idx - 1 {
                            // This is the direct comparison we just made
                            assert(nums.spec_index(i) != nums.spec_index(write_idx as int));
                        } else {
                            // For i < write_idx - 1, we have nums[i] < nums[write_idx-1] < nums[read_idx]
                            assert(nums.spec_index(i) < nums.spec_index((write_idx - 1) as int));
                            assert(nums.spec_index((write_idx - 1) as int) < orig_nums.spec_index(read_idx as int));
                            assert(nums.spec_index(write_idx as int) == orig_nums.spec_index(read_idx as int));
                        }
                    }
                };
                
                // Prove ordering is maintained
                assert forall|i: int| 0 <= i < write_idx implies nums.spec_index(i) < nums.spec_index(write_idx as int) by {
                    if i < write_idx {
                        if i == write_idx - 1 {
                            // We know nums[read_idx] > nums[write_idx-1] from the if condition
                            // and nums[write_idx] = nums[read_idx] after the assignment
                            assert(orig_nums.spec_index(read_idx as int) > nums.spec_index((write_idx - 1) as int));
                        } else {
                            // For i < write_idx - 1, transitivity gives us the result
                            assert(nums.spec_index(i) < nums.spec_index((write_idx - 1) as int));
                        }
                    }
                };
            }
            
            write_idx += 1;
        }
        
        read_idx += 1;
        
        proof {
            // Maintain the invariant that all processed elements are represented
            let old_read_idx = read_idx - 1;
            assert(orig_nums.spec_index(old_read_idx as int) in nums@.subrange(0, write_idx as int));
        }
    }
    
    proof {
        // Final proof: all original elements are represented
        assert forall|i: int| 0 <= i < old(nums).len() implies old(nums).spec_index(i) in nums@.subrange(0, write_idx as int) by {
            // This follows from the loop invariant when read_idx reached nums.len()
            assert(i < read_idx);
            assert(orig_nums.spec_index(i) in nums@.subrange(0, write_idx as int));
            assert(orig_nums == old(nums)@);
        };
        
        // All elements in result come from original
        assert forall|i: int| 0 <= i < write_idx implies nums.spec_index(i) in old(nums)@ by {
            assert(nums.spec_index(i) in orig_nums);
            assert(orig_nums == old(nums)@);
        };
    }
    
    write_idx
}

}