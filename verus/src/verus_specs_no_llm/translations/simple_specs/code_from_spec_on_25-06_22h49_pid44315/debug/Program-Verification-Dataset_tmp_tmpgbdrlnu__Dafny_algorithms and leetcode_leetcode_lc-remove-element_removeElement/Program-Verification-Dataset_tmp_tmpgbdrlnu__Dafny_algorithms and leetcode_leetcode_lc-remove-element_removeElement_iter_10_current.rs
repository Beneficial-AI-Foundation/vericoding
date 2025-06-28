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
            // All elements in the write portion existed in the original vector from positions 0..read_index
            forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < read_index && nums[k as int] == original_nums[j],
            // Elements beyond read_index are unchanged
            forall|k: int| read_index <= k < nums.len() ==> nums[k as int] == original_nums[k as int],
            // The write portion contains exactly the non-val elements from the read portion
            forall|j: int| 0 <= j < read_index && original_nums[j] != val ==> 
                exists|k: int| 0 <= k < write_index && nums[k as int] == original_nums[j],
    {
        if nums[read_index as int] != val {
            nums.set(write_index, nums[read_index as int]);
            
            // Proof: The element we just wrote exists in the original at position read_index
            assert(exists|j: int| 0 <= j < read_index + 1 && nums[write_index as int] == original_nums[j]) by {
                assert(nums[write_index as int] == original_nums[read_index as int]);
            }
            
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }
    
    // At this point, we've processed all elements
    assert(read_index == original_nums.len());
    
    // Prove that all elements in write portion exist somewhere in original
    assert(forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < original_nums.len() && nums[k as int] == original_nums[j]) by {
        assert(forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < read_index && nums[k as int] == original_nums[j]);
        assert(read_index == original_nums.len());
    }
    
    nums.truncate(write_index);
    
    // After truncation, nums.len() == write_index
    assert(nums.len() == write_index);
    
    write_index
}

}