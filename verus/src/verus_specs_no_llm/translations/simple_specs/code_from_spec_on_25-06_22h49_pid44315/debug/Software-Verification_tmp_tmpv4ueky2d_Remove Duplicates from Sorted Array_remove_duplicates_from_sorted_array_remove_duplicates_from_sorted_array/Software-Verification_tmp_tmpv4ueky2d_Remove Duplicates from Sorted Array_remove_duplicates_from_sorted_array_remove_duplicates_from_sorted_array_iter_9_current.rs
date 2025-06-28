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
                let last_elem = result[result.len() - 1];
                
                // Prove last_elem < current using the fact that nums is sorted
                assert(appears_in_prefix(nums, last_elem, idx));
                
                // Get a witness for where last_elem appears
                let j = choose|j: int| 0 <= j < idx && nums[j] == last_elem;
                assert(0 <= j < idx);
                assert(nums[j] == last_elem);
                assert(j < idx);
                
                // Since nums is sorted and j < idx
                assert(nums[j] <= nums[idx]) by {
                    assert(is_sorted(nums));
                    assert(0 <= j < idx < nums.len());
                }
                
                // Since last_elem != current, we have strict inequality
                assert(last_elem < current) by {
                    assert(last_elem == nums[j]);
                    assert(current == nums[idx]);
                    assert(nums[j] <= nums[idx]);
                    assert(last_elem <= current);
                    // Since last_elem != current and last_elem <= current
                    assert(last_elem < current);
                }
            }
            
            result = result.push(current);
            
            // Help verify the invariants after push
            assert(is_sorted_and_distinct(result)) by {
                if result.len() <= 1 {
                    // Trivially sorted and distinct
                } else {
                    // We just proved last_elem < current above
                    let old_len = result.len() - 1;
                    assert(forall|i: int, j: int| 0 <= i < j < old_len ==> result[i] < result[j]);
                    assert(forall|i: int| 0 <= i < old_len ==> result[i] < current);
                }
            }
        }
        
        idx = idx + 1;
    }
    
    // Prove same_elements after the loop
    assert(same_elements(nums, result)) by {
        assert(forall|x: int| contains(nums, x) <==> contains(result, x)) by {
            // Forward direction: if x is in nums, it's in result
            assert(forall|x: int| contains(nums, x) ==> contains(result, x)) by {
                forall|x: int| contains(nums, x) implies {
                    // x appears somewhere in nums, so it appears in prefix of length nums.len()
                    assert(appears_in_prefix(nums, x, nums.len()));
                    // By invariant, it must be in result
                    assert(contains(result, x));
                }
            }
            
            // Backward direction: if x is in result, it's in nums
            assert(forall|x: int| contains(result, x) ==> contains(nums, x)) by {
                // This follows directly from the invariant
                assert(forall|i: int| 0 <= i < result.len() ==> contains(nums, result[i]));
            }
        }
    }
    
    result
}

}