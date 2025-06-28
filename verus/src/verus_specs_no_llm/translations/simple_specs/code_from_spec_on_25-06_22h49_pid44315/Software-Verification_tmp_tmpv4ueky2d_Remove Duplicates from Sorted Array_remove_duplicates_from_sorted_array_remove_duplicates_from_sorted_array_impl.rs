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
                
                // We know there exists some j where last_elem appears
                assert(exists|j: int| 0 <= j < idx && j < nums.len() && nums[j] == last_elem);
                
                // Prove the strict inequality
                assert(last_elem < current) by {
                    // Since last_elem appears in prefix and nums is sorted
                    assert(forall|j: int| (0 <= j < idx && j < nums.len() && nums[j] == last_elem) ==> 
                           nums[j] <= nums[idx]);
                    
                    // Since last_elem != current and they're in sorted order
                    assert(last_elem <= current);
                    assert(last_elem != current);
                    assert(last_elem < current);
                }
            }
            
            let old_result = result;
            result = result.push(current);
            
            // Help verify that the new result maintains sorted_and_distinct
            assert(is_sorted_and_distinct(result)) by {
                if old_result.len() == 0 {
                    // Single element is trivially sorted and distinct
                    assert(result.len() == 1);
                } else {
                    // We proved last_elem < current above
                    let last_elem = old_result[old_result.len() - 1];
                    assert(last_elem < current);
                    
                    // The old part is still sorted and distinct
                    assert(forall|i: int, j: int| 0 <= i < j < old_result.len() ==> old_result[i] < old_result[j]);
                    
                    // The new element is greater than all previous elements
                    assert(forall|i: int| 0 <= i < old_result.len() ==> old_result[i] < current);
                    
                    // Therefore the entire new sequence is sorted and distinct
                    assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j]);
                }
            }
            
            // Help verify the appears_in_prefix invariant
            assert(forall|i: int| 0 <= i < result.len() ==> appears_in_prefix(nums, result[i], idx + 1)) by {
                forall|i: int| 0 <= i < result.len() implies {
                    if i < old_result.len() {
                        assert(appears_in_prefix(nums, result[i], idx));
                        assert(appears_in_prefix(nums, result[i], idx + 1));
                    } else {
                        assert(i == old_result.len());
                        assert(result[i] == current);
                        assert(result[i] == nums[idx]);
                        assert(appears_in_prefix(nums, result[i], idx + 1));
                    }
                }
            }
        }
        
        idx = idx + 1;
    }
    
    // Prove same_elements after the loop
    assert(same_elements(nums, result)) by {
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
            forall|x: int| contains(result, x) implies {
                let i = choose|i: int| 0 <= i < result.len() && result[i] == x;
                assert(appears_in_prefix(nums, result[i], nums.len()));
                assert(contains(nums, x));
            }
        }
    }
    
    result
}

}