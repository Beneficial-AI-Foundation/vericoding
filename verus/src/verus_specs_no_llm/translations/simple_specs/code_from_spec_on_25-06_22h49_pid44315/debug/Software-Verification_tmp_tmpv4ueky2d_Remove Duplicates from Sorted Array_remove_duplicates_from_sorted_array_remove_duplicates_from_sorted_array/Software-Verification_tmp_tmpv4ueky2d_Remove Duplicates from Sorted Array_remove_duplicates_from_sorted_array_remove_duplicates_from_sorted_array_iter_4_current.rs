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
            // All elements in result come from the first idx elements of nums
            forall|i: int| 0 <= i < result.len() ==> 
                exists|j: int| 0 <= j < idx && nums[j] == result[i],
            // Every unique element in first idx positions appears in result
            forall|j: int| 0 <= j < idx ==> contains(result, nums[j]),
            // No element appears twice in result
            forall|i: int, k: int| 0 <= i < k < result.len() ==> result[i] != result[k]
    {
        let current = nums[idx];
        
        if result.len() == 0 || result[result.len() - 1] != current {
            result = result.push(current);
        }
        
        idx = idx + 1;
    }
    
    result
}

}