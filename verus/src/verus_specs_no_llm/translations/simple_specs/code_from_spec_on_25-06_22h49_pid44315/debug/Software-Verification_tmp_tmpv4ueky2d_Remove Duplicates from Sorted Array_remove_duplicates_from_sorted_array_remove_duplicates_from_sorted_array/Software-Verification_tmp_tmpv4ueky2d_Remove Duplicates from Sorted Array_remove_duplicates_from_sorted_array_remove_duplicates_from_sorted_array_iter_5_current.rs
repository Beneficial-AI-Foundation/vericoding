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
            // Every unique element in first idx positions appears in result
            forall|j: int| 0 <= j < idx ==> contains(result, nums[j]),
            // Elements in result are from first idx elements of nums
            forall|i: int| 0 <= i < result.len() ==> 
                exists|j: int| 0 <= j < idx && nums[j] == result[i],
            // Result maintains sortedness from original
            forall|i: int| 0 <= i < result.len() ==> 
                forall|k: int| 0 <= k < nums.len() && nums[k] == result[i] ==> 
                    forall|j: int| 0 <= j < i ==> result[j] < nums[k]
    {
        let current = nums[idx];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            // Prove that adding current maintains sorted and distinct property
            assert(forall|i: int| 0 <= i < result.len() ==> result[i] < current) by {
                if result.len() > 0 {
                    // Since nums is sorted and we've processed up to idx-1,
                    // and current comes from nums[idx], current >= all previous elements
                    assert(forall|j: int| 0 <= j < idx ==> nums[j] <= current);
                    // Since result contains only elements from first idx positions
                    // and we only add elements that are different from the last one,
                    // all elements in result are < current
                }
            };
            result = result.push(current);
        }
        
        idx = idx + 1;
    }
    
    // Prove same_elements postcondition
    assert(same_elements(nums, result)) by {
        assert(forall|x: int| contains(nums, x) <==> contains(result, x)) by {
            assert(forall|x: int| contains(nums, x) ==> contains(result, x)) by {
                // Every element in nums is added to result at least once
            };
            assert(forall|x: int| contains(result, x) ==> contains(nums, x)) by {
                // Every element in result comes from nums (by invariant)
            };
        }
    };
    
    result
}

}