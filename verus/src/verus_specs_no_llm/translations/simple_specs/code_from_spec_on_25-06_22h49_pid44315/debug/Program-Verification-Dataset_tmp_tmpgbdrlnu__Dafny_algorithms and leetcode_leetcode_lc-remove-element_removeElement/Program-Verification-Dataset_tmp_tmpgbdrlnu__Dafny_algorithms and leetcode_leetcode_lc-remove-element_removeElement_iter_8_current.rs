use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures
        i <= old(nums).len(),
        i == nums.len(),
        forall|k: int| 0 <= k < i ==> nums[k as int] != val,
        forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < old(nums).len() && nums[k as int] == old(nums)[j],
{
    let ghost original_nums = *nums;
    let mut write_index: usize = 0;
    let mut read_index: usize = 0;
    
    while read_index < nums.len()
        invariant
            write_index <= read_index,
            read_index <= nums.len(),
            write_index <= nums.len(),
            nums.len() == original_nums.len(),
            // All elements in the write portion don't equal val
            forall|k: int| 0 <= k < write_index ==> nums[k as int] != val,
            // All elements in the write portion existed in the original vector
            forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < original_nums.len() && nums[k as int] == original_nums[j],
            // Elements beyond read_index are preserved from original
            forall|k: int| read_index < k < nums.len() ==> nums[k as int] == original_nums[k as int],
            // Key invariant: elements in write portion come from elements we've read
            forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < read_index && nums[k as int] == original_nums[j] && original_nums[j] != val,
    {
        if nums[read_index as int] != val {
            // Copy the element that's not equal to val
            nums.set(write_index, nums[read_index as int]);
            
            // Proof that the element we just wrote exists in original
            assert(nums[write_index as int] == original_nums[read_index as int]);
            assert(original_nums[read_index as int] != val);
            
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }
    
    // At this point, we've processed all elements
    assert(read_index == original_nums.len());
    
    // Truncate the vector to remove unused elements
    nums.truncate(write_index);
    
    // Prove postconditions
    assert(write_index <= original_nums.len());
    assert(write_index == nums.len());
    
    // Prove that no element in the result equals val
    assert(forall|k: int| 0 <= k < write_index ==> nums[k as int] != val);
    
    // Prove that every element in result existed in original
    assert(forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < original_nums.len() && nums[k as int] == original_nums[j]);
    
    write_index
}

}