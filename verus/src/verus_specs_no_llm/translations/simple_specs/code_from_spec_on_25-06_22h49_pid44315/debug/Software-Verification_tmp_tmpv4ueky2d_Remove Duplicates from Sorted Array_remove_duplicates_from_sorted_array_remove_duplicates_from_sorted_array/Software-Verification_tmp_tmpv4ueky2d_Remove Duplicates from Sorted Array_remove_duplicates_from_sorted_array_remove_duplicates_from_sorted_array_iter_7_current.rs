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
            // Every unique element that appears in first idx positions appears in result
            forall|val: int| appears_in_prefix(nums, val, idx) ==> contains(result, val),
            // No element in result that doesn't appear in first idx positions
            forall|i: int| 0 <= i < result.len() ==> appears_in_prefix(nums, result[i], idx),
            // If we have processed some elements, result is non-empty
            idx > 0 ==> result.len() > 0,
    {
        let current = nums[idx];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            // Prove that adding current maintains sorted and distinct property
            if result.len() > 0 {
                // Key insight: since nums is sorted and current = nums[idx]
                let last_elem = result[result.len() - 1];
                
                // Prove last_elem < current
                assert(appears_in_prefix(nums, last_elem, idx));
                assert(exists|j: int| 0 <= j < idx && nums[j] == last_elem);
                
                // Since nums is sorted and j < idx, we have nums[j] <= nums[idx]
                // Since last_elem != current and last_elem = nums[j], current = nums[idx]
                // We have last_elem <= current, and since they're different: last_elem < current
                assert(last_elem < current);
                
                // Prove all elements in result are < current
                assert(forall|i: int| 0 <= i < result.len() ==> result[i] < current) by {
                    assert(forall|i: int| 0 <= i < result.len() ==> result[i] <= last_elem);
                    assert(last_elem < current);
                };
            }
            
            result = result.push(current);
            
            // Prove the new result maintains is_sorted_and_distinct
            assert(is_sorted_and_distinct(result));
        }
        
        idx = idx + 1;
    }
    
    // Final proof of same_elements
    assert(idx == nums.len());
    
    // Prove forward direction: contains(nums, x) ==> contains(result, x)
    assert(forall|x: int| contains(nums, x) ==> contains(result, x)) by {
        assert(forall|x: int| contains(nums, x) ==> appears_in_prefix(nums, x, nums.len()));
    };
    
    // Prove backward direction: contains(result, x) ==> contains(nums, x)
    assert(forall|x: int| contains(result, x) ==> contains(nums, x));
    
    // Therefore same_elements holds
    assert(same_elements(nums, result));
    
    result
}

}