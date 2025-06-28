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
            // Additional invariant: result elements are in increasing order with nums prefix
            forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < idx ==> 
                (nums[j] < result[i] ==> exists|k: int| k > j && k < idx && nums[k] == result[i]),
    {
        let current = nums[idx];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            // Prove that adding current maintains sorted and distinct property
            if result.len() > 0 {
                let last_elem = result[result.len() - 1];
                
                // Prove last_elem < current using the fact that nums is sorted
                // and we haven't seen current before in result
                assert(appears_in_prefix(nums, last_elem, idx));
                
                // Since nums is sorted, and current appears at position idx,
                // and last_elem appears before idx, we need to show last_elem < current
                assert(forall|j: int| 0 <= j < idx && nums[j] == last_elem ==> nums[j] <= nums[idx]) by {
                    assert(is_sorted(nums));
                };
                
                // Since last_elem != current, and nums is sorted, last_elem < current
                assert(last_elem != current);
                assert(exists|j: int| 0 <= j < idx && nums[j] == last_elem);
                
                // Use sorted property to conclude last_elem < current
                assert(last_elem < current) by {
                    let j = choose|j: int| 0 <= j < idx && nums[j] == last_elem;
                    assert(nums[j] <= nums[idx]);
                    assert(last_elem == nums[j]);
                    assert(current == nums[idx]);
                    assert(last_elem <= current);
                    if last_elem == current {
                        // This would contradict our condition
                        assert(false);
                    }
                };
            }
            
            result = result.push(current);
        }
        
        idx = idx + 1;
    }
    
    // Prove same_elements after the loop
    assert(forall|x: int| contains(nums, x) <==> contains(result, x)) by {
        // Forward direction
        assert(forall|x: int| contains(nums, x) ==> contains(result, x)) by {
            forall|x: int| contains(nums, x) implies {
                assert(appears_in_prefix(nums, x, nums.len()));
                assert(contains(result, x));
            }
        };
        
        // Backward direction follows from invariant
        assert(forall|x: int| contains(result, x) ==> contains(nums, x));
    };
    
    result
}

}