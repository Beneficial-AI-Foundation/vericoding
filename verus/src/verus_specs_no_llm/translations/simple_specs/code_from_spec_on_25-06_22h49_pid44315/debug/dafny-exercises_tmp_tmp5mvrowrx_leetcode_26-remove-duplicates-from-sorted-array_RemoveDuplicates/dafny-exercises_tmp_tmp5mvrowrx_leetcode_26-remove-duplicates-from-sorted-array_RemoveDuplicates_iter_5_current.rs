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
            nums.set(write_idx, nums[read_idx]);
            
            // Proof that the new element maintains sortedness
            assert(nums.spec_index(write_idx) == nums.spec_index(read_idx as int));
            assert(nums.spec_index(read_idx as int) == orig_nums.spec_index(read_idx as int));
            assert(nums.spec_index(write_idx - 1) < nums.spec_index(read_idx as int)) by {
                assert(nums.spec_index(write_idx - 1) != nums.spec_index(read_idx as int));
                assert(nums.spec_index(write_idx - 1) in orig_nums);
                assert(nums.spec_index(read_idx as int) == orig_nums.spec_index(read_idx as int));
                // Since original array is sorted and elements are different, strict inequality holds
            };
            
            write_idx += 1;
        }
        
        read_idx += 1;
    }
    
    // Final proof assertions for postconditions
    assert(forall|i: int| 0 <= i < old(nums).len() ==> old(nums).spec_index(i) in nums@.subrange(0, write_idx as int)) by {
        assert(forall|k: int| 0 <= k < orig_nums.len() ==> orig_nums.spec_index(k) in nums@.subrange(0, write_idx as int));
        assert(orig_nums == old(nums)@);
    };
    
    write_idx
}

}