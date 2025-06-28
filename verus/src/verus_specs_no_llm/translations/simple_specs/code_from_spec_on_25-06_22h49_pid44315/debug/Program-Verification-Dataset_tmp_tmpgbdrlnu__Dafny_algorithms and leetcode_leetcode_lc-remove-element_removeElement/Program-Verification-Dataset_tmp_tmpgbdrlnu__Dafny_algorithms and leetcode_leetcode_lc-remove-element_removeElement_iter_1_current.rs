use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures
        i <= old(nums).len(),
        i == nums.len(),
        forall|k: int| 0 <= k < i ==> nums[k] != val,
        forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < old(nums).len() && nums[k as int] == old(nums)[j],
{
    let mut write_index: usize = 0;
    let mut read_index: usize = 0;
    
    while read_index < nums.len()
        invariant
            write_index <= read_index,
            read_index <= nums.len(),
            write_index <= nums.len(),
            forall|k: int| 0 <= k < write_index ==> nums[k] != val,
            forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < read_index && nums[k] == old(nums)[j],
    {
        if nums[read_index] != val {
            nums.set(write_index, nums[read_index]);
            write_index += 1;
        }
        read_index += 1;
    }
    
    // Truncate the vector to the new size
    nums.truncate(write_index);
    
    write_index
}

}

The implementation:




   - The returned length is at most the original length
   - The returned length equals the final vector length
   - All elements in the result range don't equal `val`
   - All elements in the result existed in the original vector


This implementation satisfies the constraint that elements at indices `[0, returned_length)` are not equal to `val`, while efficiently removing all occurrences of the target value.