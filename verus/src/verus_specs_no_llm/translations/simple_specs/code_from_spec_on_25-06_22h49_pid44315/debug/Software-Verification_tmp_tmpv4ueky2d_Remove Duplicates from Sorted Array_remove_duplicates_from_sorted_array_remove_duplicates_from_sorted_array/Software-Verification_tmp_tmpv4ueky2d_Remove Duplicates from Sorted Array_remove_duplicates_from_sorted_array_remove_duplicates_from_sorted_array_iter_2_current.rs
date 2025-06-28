use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_sorted(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
}

spec fn is_sorted_and_distinct(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j]
}

spec fn contains(nums: Seq<int>, val: int) -> bool {
    exists|i: int| 0 <= i < nums.len() && nums[i] == val
}

spec fn same_elements(s1: Seq<int>, s2: Seq<int>) -> bool {
    forall|x: int| contains(s1, x) <==> contains(s2, x)
}

fn remove_duplicates_from_sorted_array(nums: Seq<int>) -> (result: Seq<int>)
    requires
        is_sorted(nums),
        1 <= nums.len() <= 30000,
        forall|i: int| 0 <= i < nums.len() ==> -100 <= nums[i] <= 100
    ensures
        is_sorted_and_distinct(result),
        same_elements(nums, result)
{
    let mut result = Seq::empty();
    let mut idx = 0;
    
    while idx < nums.len()
        invariant
            0 <= idx <= nums.len(),
            is_sorted_and_distinct(result),
            // All elements in result come from nums
            forall|i: int| 0 <= i < result.len() ==> contains(nums, result[i]),
            // All processed elements are represented in result
            forall|j: int| 0 <= j < idx ==> contains(result, nums[j]),
            // All elements in result come from processed part
            forall|i: int| 0 <= i < result.len() ==> 
                exists|j: int| 0 <= j < idx && nums[j] == result[i],
            // Result maintains sorted property from original
            forall|i: int| 0 <= i < result.len() ==> 
                exists|j: int| 0 <= j < nums.len() && nums[j] == result[i]
    {
        let current = nums[idx];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            result = result.push(current);
            
            // Proof that adding current maintains distinctness
            assert(forall|i: int| 0 <= i < result.len() - 1 ==> result[i] < current) by {
                if result.len() > 1 {
                    // The last element before current is < current (no duplicates)
                    // All previous elements are <= last element (sorted result)
                    // Original sequence is sorted, so elements before idx are <= current
                }
            };
        }
        
        idx = idx + 1;
    }
    
    // Prove the final postcondition about same elements
    assert(same_elements(nums, result)) by {
        // Forward direction: everything in nums is in result
        assert(forall|x: int| contains(nums, x) ==> contains(result, x));
        // Backward direction: everything in result is in nums  
        assert(forall|x: int| contains(result, x) ==> contains(nums, x));
    };
    
    result
}

}