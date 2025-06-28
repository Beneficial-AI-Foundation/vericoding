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
            forall|i: int| 0 <= i < write_idx ==> nums.spec_index(i) in old(nums)@,
            // All original elements up to read_idx are represented in the first write_idx positions
            forall|k: int| 0 <= k < read_idx ==> old(nums).spec_index(k) in nums@.subrange(0, write_idx as int),
            // Preserved elements after write_idx
            forall|i: int| write_idx <= i < nums.len() ==> nums.spec_index(i) == old(nums).spec_index(i),
    {
        if nums[read_idx] != nums[write_idx - 1] {
            nums.set(write_idx, nums[read_idx]);
            write_idx += 1;
        }
        read_idx += 1;
    }
    
    write_idx
}

}

The key insights for this implementation:



   - The portion before `write_idx` contains distinct, sorted elements
   - All elements come from the original array
   - All original elements processed so far are represented in the result

   - The result contains distinct elements
   - All result elements come from the original array  
   - All original elements appear in the result subrange
   - The sorted order is maintained

The algorithm works by keeping track of the last unique element seen and only copying new elements that are different from it, taking advantage of the sorted input to detect duplicates efficiently.