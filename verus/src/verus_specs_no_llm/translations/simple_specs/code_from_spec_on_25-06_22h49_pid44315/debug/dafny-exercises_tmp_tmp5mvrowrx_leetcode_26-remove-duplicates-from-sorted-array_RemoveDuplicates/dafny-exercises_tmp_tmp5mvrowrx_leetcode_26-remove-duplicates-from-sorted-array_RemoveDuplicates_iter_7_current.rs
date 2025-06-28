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
            assert(nums.spec_index(write_idx - 1) < nums.spec_index(read_idx as int)) by {
                let ghost prev_val = nums.spec_index(write_idx - 1);
                let ghost curr_val = nums.spec_index(read_idx as int);
                
                // Current value equals original value at read_idx
                assert(curr_val == orig_nums.spec_index(read_idx as int));
                
                // Previous value exists in original array before read_idx
                assert(prev_val in orig_nums);
                
                // Since all original elements up to read_idx are in subrange [0, write_idx)
                // and prev_val is at position write_idx-1, there must be some position j < read_idx
                // in original array where orig_nums[j] == prev_val
                assert(exists|j: int| 0 <= j < read_idx && orig_nums.spec_index(j) == prev_val) by {
                    // prev_val is in the subrange [0, write_idx) which contains all elements [0, read_idx)
                    assert(forall|k: int| 0 <= k < read_idx ==> orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int));
                    assert(prev_val == nums.spec_index(write_idx - 1));
                    assert(0 <= write_idx - 1 < write_idx);
                }
                
                // By choose, we can get such a position
                let ghost j = choose|j: int| 0 <= j < read_idx && orig_nums.spec_index(j) == prev_val;
                assert(0 <= j < read_idx);
                assert(orig_nums.spec_index(j) == prev_val);
                
                // Since j < read_idx and original array is sorted
                assert(orig_nums.spec_index(j) <= orig_nums.spec_index(read_idx as int));
                assert(prev_val <= curr_val);
                
                // Since they are different (from the if condition) and prev_val <= curr_val
                assert(prev_val != curr_val);
                assert(prev_val < curr_val);
            };
            
            nums.set(write_idx, nums[read_idx]);
            write_idx += 1;
        }
        
        read_idx += 1;
    }
    
    // Final proof for completeness
    assert(forall|i: int| 0 <= i < orig_nums.len() ==> orig_nums.spec_index(i) in nums@.subrange(0, write_idx as int));
    
    write_idx
}

}