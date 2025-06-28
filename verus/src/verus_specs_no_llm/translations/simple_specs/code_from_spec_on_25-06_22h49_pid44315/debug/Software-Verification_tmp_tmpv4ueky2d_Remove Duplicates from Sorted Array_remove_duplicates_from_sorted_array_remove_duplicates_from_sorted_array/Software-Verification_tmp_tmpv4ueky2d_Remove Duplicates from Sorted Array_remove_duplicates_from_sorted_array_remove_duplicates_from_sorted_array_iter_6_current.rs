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

// Helper spec function to check if an element appears in the first k positions
spec fn appears_in_prefix(nums: Seq<int>, val: int, k: int) -> bool {
    exists|i: int| 0 <= i < k && i < nums.len() && nums[i] == val
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
            // Every element that appears in first idx positions and isn't a duplicate appears in result
            forall|val: int| appears_in_prefix(nums, val, idx) ==> contains(result, val),
            // No element in result that doesn't appear in first idx positions
            forall|i: int| 0 <= i < result.len() ==> appears_in_prefix(nums, result[i], idx),
            // If we have processed some elements, the last element in result equals the last unique element processed
            idx > 0 ==> result.len() > 0,
            // Maintain relationship with sorted input
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < idx && result[i] == nums[j] ==>
                forall|k: int| 0 <= k < i ==> result[k] < nums[j]
    {
        let current = nums[idx];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            // Prove that adding current maintains sorted and distinct property
            if result.len() > 0 {
                // Key insight: since nums is sorted and we've seen all elements up to idx-1,
                // and current = nums[idx], we know current >= all previous elements
                assert(forall|j: int| 0 <= j < idx ==> nums[j] <= nums[idx]);
                
                // Since result contains only elements from the first idx positions,
                // and current is different from the last element in result,
                // current must be > all elements in result
                let last_idx = result.len() - 1;
                assert(result[last_idx] != current);
                assert(appears_in_prefix(nums, result[last_idx], idx));
                
                // Since nums is sorted and result[last_idx] appears before position idx,
                // and current = nums[idx], we have result[last_idx] <= current
                // Since they're not equal, result[last_idx] < current
                assert(result[last_idx] < current);
                
                // By transitivity and the fact that result is already sorted,
                // all elements in result are < current
                assert(forall|i: int| 0 <= i < result.len() ==> result[i] < current);
            }
            
            result = result.push(current);
        }
        
        idx = idx + 1;
    }
    
    // Prove same_elements postcondition
    assert(forall|x: int| contains(nums, x) <==> contains(result, x)) by {
        // Forward direction: if x is in nums, then x is in result
        assert(forall|x: int| contains(nums, x) ==> contains(result, x)) by {
            // Since we processed all elements (idx == nums.len()),
            // every element that appears in nums appears in some prefix we processed
            assert(forall|x: int| contains(nums, x) ==> appears_in_prefix(nums, x, nums.len()));
            // By our invariant, every element in any prefix appears in result
        };
        
        // Backward direction: if x is in result, then x is in nums  
        assert(forall|x: int| contains(result, x) ==> contains(nums, x)) by {
            // By invariant, all elements in result come from nums
        };
    };
    
    result
}

}