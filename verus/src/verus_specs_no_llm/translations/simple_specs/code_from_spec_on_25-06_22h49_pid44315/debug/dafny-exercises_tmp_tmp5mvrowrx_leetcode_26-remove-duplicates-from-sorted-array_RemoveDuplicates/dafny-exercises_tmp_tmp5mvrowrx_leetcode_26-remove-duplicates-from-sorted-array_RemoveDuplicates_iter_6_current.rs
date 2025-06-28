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
            // Proof assertions before modification
            assert(nums.spec_index(read_idx as int) == orig_nums.spec_index(read_idx as int));
            assert(nums.spec_index(write_idx - 1) in orig_nums);
            
            // Since original array is sorted and current element is different from previous unique element
            assert(nums.spec_index(write_idx - 1) < nums.spec_index(read_idx as int)) by {
                // The element at write_idx-1 appears before read_idx in the original sorted array
                // and they are different, so strict inequality must hold
                let ghost prev_val = nums.spec_index(write_idx - 1);
                let ghost curr_val = nums.spec_index(read_idx as int);
                assert(prev_val != curr_val);
                assert(prev_val in orig_nums);
                assert(curr_val == orig_nums.spec_index(read_idx as int));
                
                // Find where prev_val appears in orig_nums
                assert(exists|pos: int| 0 <= pos < read_idx && orig_nums.spec_index(pos) == prev_val) by {
                    assert(forall|k: int| 0 <= k < read_idx ==> orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int));
                    assert(prev_val in nums@.subrange(0, write_idx as int));
                };
            };
            
            nums.set(write_idx, nums[read_idx]);
            write_idx += 1;
        }
        
        read_idx += 1;
    }
    
    // Final proof for completeness - all original elements are represented
    assert(forall|i: int| 0 <= i < orig_nums.len() ==> orig_nums.spec_index(i) in nums@.subrange(0, write_idx as int)) by {
        // This follows from the loop invariant when read_idx reaches nums.len()
        assert(read_idx == nums.len());
        assert(forall|k: int| 0 <= k < read_idx ==> orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int));
        assert(orig_nums.len() == nums.len());
    };
    
    write_idx
}

}