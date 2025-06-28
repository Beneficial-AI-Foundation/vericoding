use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(nums: &mut Vec<int>) -> (num_length: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
    ensures 
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> exists|k: int| 0 <= k < old(nums).len() && nums[i] == old(nums)[k],
        forall|k: int| 0 <= k < old(nums).len() ==> exists|i: int| 0 <= i < num_length && old(nums)[k] == nums[i]
{
    if nums.len() == 0 {
        return 0;
    }

    let ghost original_nums = *nums;
    let mut write_index: usize = 1;
    let mut read_index: usize = 1;

    while read_index < nums.len()
        invariant
            1 <= write_index <= read_index + 1,
            read_index <= nums.len(),
            write_index <= nums.len(),
            nums.len() == original_nums.len(),
            // All elements in result come from original array
            forall|i: int| 0 <= i < write_index ==> exists|k: int| 0 <= k < original_nums.len() && nums[i] == original_nums[k],
            // All processed original elements are represented in result
            forall|k: int| 0 <= k < read_index ==> exists|i: int| 0 <= i < write_index && original_nums[k] == nums[i],
            // Maintain sorted order in result portion
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] <= nums[j],
            // First element unchanged
            nums[0] == original_nums[0],
            // Original array was sorted
            forall|i: int, j: int| 0 <= i < j < original_nums.len() ==> original_nums[i] <= original_nums[j],
            // Distinctness in result portion - adjacent elements are different
            forall|i: int| 0 <= i < write_index - 1 ==> nums[i] != nums[i + 1],
    {
        if nums[read_index] != nums[write_index - 1] {
            nums.set(write_index, nums[read_index]);
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }

    proof {
        // Prove distinctness from adjacent distinctness and sorted property
        assert forall|i: int, j: int| 0 <= i < j < write_index implies nums[i] != nums[j] by {
            if 0 <= i < j < write_index {
                // Key insight: in a sorted array, if adjacent elements are distinct,
                // then all elements are distinct
                
                // We'll prove this by showing nums[i] < nums[j] (strict inequality)
                // Since the array is sorted: nums[i] <= nums[i+1] <= ... <= nums[j]
                // And we know adjacent elements are distinct: nums[k] != nums[k+1] for all valid k
                
                // Build a chain of strict inequalities
                let mut k = i;
                while k < j
                    invariant
                        i <= k < j,
                        nums[i] <= nums[k],
                        k == i || nums[i] < nums[k],
                {
                    // nums[k] <= nums[k+1] from sortedness
                    assert(nums[k] <= nums[k + 1]);
                    // nums[k] != nums[k+1] from adjacent distinctness  
                    assert(nums[k] != nums[k + 1]);
                    // Therefore nums[k] < nums[k+1]
                    assert(nums[k] < nums[k + 1]);
                    k = k + 1;
                }
                
                // Now we have nums[i] < nums[j], so nums[i] != nums[j]
                assert(nums[i] < nums[j]);
                assert(nums[i] != nums[j]);
            }
        };
    }

    write_index
}

fn Testing() -> (result: (int, int, int, int))
{
    (0, 0, 0, 0)
}

}