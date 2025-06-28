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
            // Key property: all original elements are represented
            forall|k: int| 0 <= k < orig_nums.len() ==> orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int),
    {
        if nums[read_idx] != nums[write_idx - 1] {
            // Prove that the new element maintains sortedness
            assert(nums[read_idx] > nums[write_idx - 1]) by {
                assert(orig_nums.spec_index(read_idx as int) >= orig_nums.spec_index((write_idx - 1) as int));
                assert(nums.spec_index(read_idx as int) == orig_nums.spec_index(read_idx as int));
                assert(nums.spec_index((write_idx - 1) as int) in orig_nums);
            }
            
            nums.set(write_idx, nums[read_idx]);
            
            // Prove invariants are maintained after assignment
            assert(forall|i: int| 0 <= i < write_idx + 1 ==> nums.spec_index(i) in orig_nums) by {
                assert(nums.spec_index(write_idx as int) == orig_nums.spec_index(read_idx as int));
            }
            
            assert(forall|i: int, j: int| 0 <= i < j < write_idx + 1 ==> nums.spec_index(i) < nums.spec_index(j)) by {
                assert(nums.spec_index(write_idx as int) > nums.spec_index((write_idx - 1) as int));
            }
            
            write_idx += 1;
        }
        
        // Prove that all elements up to read_idx+1 are still represented
        assert(forall|k: int| 0 <= k < read_idx + 1 ==> orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int)) by {
            if read_idx < orig_nums.len() {
                if nums[read_idx] == nums[write_idx - 1] {
                    // The element at read_idx is the same as one already in our result
                    assert(orig_nums.spec_index(read_idx as int) == nums.spec_index((write_idx - 1) as int));
                }
            }
        }
        
        read_idx += 1;
    }
    
    // Final assertions to help prove postconditions
    assert(forall|i: int| 0 <= i < orig_nums.len() ==> orig_nums.spec_index(i) in nums@.subrange(0, write_idx as int));
    assert(forall|i: int| 0 <= i < write_idx ==> nums.spec_index(i) in orig_nums);
    assert(forall|i: int, j: int| 0 <= i < j < write_idx ==> nums.spec_index(i) != nums.spec_index(j));
    assert(forall|i: int, j: int| 0 <= i < j < write_idx ==> nums.spec_index(i) < nums.spec_index(j));
    
    write_idx
}

}