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
            forall|k: int| read_index <= k < nums.len() ==> nums[k as int] == original_nums[k as int],
    {
        if nums[read_index] != val {
            // Copy the element that's not equal to val
            let current_val = nums[read_index];
            
            proof {
                assert(current_val == original_nums[read_index as int]);
                assert(exists|j: int| 0 <= j < original_nums.len() && current_val == original_nums[j]) by {
                    assert(current_val == original_nums[read_index as int] && 0 <= read_index < original_nums.len());
                }
            }
            
            nums.set(write_index, current_val);
            
            proof {
                // Maintain invariant that all elements in write portion don't equal val
                assert(forall|k: int| 0 <= k < write_index ==> nums[k as int] != val);
                assert(nums[write_index as int] != val);
                assert(forall|k: int| 0 <= k < write_index + 1 ==> nums[k as int] != val);
                
                // Maintain invariant that all elements in write portion existed in original
                assert(forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < original_nums.len() && nums[k as int] == original_nums[j]);
                assert(exists|j: int| 0 <= j < original_nums.len() && nums[write_index as int] == original_nums[j]);
                assert(forall|k: int| 0 <= k < write_index + 1 ==> exists|j: int| 0 <= j < original_nums.len() && nums[k as int] == original_nums[j]);
                
                // Maintain invariant about elements beyond read_index
                assert(forall|k: int| read_index + 1 <= k < nums.len() ==> nums[k as int] == original_nums[k as int]);
            }
            
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }
    
    // Prove properties before truncation
    proof {
        assert(forall|k: int| 0 <= k < write_index ==> nums[k as int] != val);
        assert(forall|k: int| 0 <= k < write_index ==> exists|j: int| 0 <= j < original_nums.len() && nums[k as int] == original_nums[j]);
    }
    
    // Truncate the vector to remove unused elements
    nums.truncate(write_index);
    
    proof {
        assert(nums.len() == write_index);
        assert(forall|k: int| 0 <= k < nums.len() ==> nums[k as int] != val);
        assert(forall|k: int| 0 <= k < nums.len() ==> exists|j: int| 0 <= j < original_nums.len() && nums[k as int] == original_nums[j]);
    }
    
    write_index
}

}