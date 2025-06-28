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
            // Preserved elements after write_idx (not strictly necessary for correctness but helps reasoning)
            forall|i: int| write_idx <= i < nums.len() ==> nums.spec_index(i) == orig_nums.spec_index(i),
            // First element is preserved
            nums.spec_index(0) == orig_nums.spec_index(0),
            // Maintain sorted property for processed portion
            forall|i: int| 1 <= i < write_idx ==> nums.spec_index(i-1) < nums.spec_index(i),
    {
        if nums[read_idx] != nums[write_idx - 1] {
            proof {
                // The new element is greater than the last unique element
                assert(orig_nums.spec_index(read_idx as int) >= orig_nums.spec_index((read_idx - 1) as int));
                assert(nums.spec_index((write_idx - 1) as int) in nums@.subrange(0, write_idx as int));
            }
            nums.set(write_idx, nums[read_idx]);
            write_idx += 1;
            proof {
                // Prove that the new element maintains distinctness and ordering
                assert forall|i: int| 0 <= i < write_idx - 1 implies nums.spec_index(i) < nums.spec_index((write_idx - 1) as int) by {
                    if i < write_idx - 1 {
                        assert(nums.spec_index(i) in nums@.subrange(0, (write_idx - 1) as int));
                        assert(nums.spec_index(i) < nums.spec_index((write_idx - 2) as int));
                        assert(nums.spec_index((write_idx - 2) as int) < nums.spec_index((write_idx - 1) as int));
                    }
                };
            }
        }
        read_idx += 1;
        proof {
            // Maintain the invariant that all processed elements are represented
            assert forall|k: int| 0 <= k < read_idx implies orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int) by {
                if k < read_idx - 1 {
                    // Previous invariant covers this
                } else if k == read_idx - 1 {
                    if nums.spec_index((read_idx - 1) as int) != nums.spec_index((write_idx - 1) as int) {
                        // We just added it
                    } else {
                        // It's already represented by an earlier element
                        assert(orig_nums.spec_index(k) in nums@.subrange(0, (write_idx - 1) as int));
                    }
                }
            };
        }
    }
    
    proof {
        // Final proof obligations
        assert forall|i: int| 0 <= i < old(nums).len() implies old(nums).spec_index(i) in nums@.subrange(0, write_idx as int) by {
            assert(orig_nums.spec_index(i) in nums@.subrange(0, write_idx as int));
        };
        
        assert forall|i: int| 0 <= i < write_idx implies nums.spec_index(i) in old(nums)@ by {
            assert(nums.spec_index(i) in orig_nums);
        };
    }
    
    write_idx
}

}