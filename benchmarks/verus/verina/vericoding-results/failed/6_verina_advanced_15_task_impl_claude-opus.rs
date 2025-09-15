// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed invariants to properly track the existence of increasing triplets */
    if nums.len() < 3 {
        return false;
    }
    
    let mut first = i32::MAX;
    let mut second = i32::MAX;
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            first <= second,
            second < i32::MAX ==> exists|j: int| 0 <= j < i && nums[j] < second,
            first < second ==> exists|j: int, k: int| 0 <= j < k && k < i && nums[j] <= first && first < nums[k] && nums[k] <= second,
            forall|a: int, b: int, c: int| 0 <= a < b && b < c && c < i ==> !(nums[a] < nums[b] && nums[b] < nums[c]),
        decreases nums.len() - i
    {
        if nums[i] <= first {
            first = nums[i];
        } else if nums[i] <= second {
            second = nums[i];
            assert(first < second);
        } else {
            assert(first < second);
            assert(second < nums[i]);
            assert(exists|j: int, k: int| 0 <= j < k && k < i && nums[j] <= first && first < nums[k] && nums[k] <= second);
            return true;
        }
        i = i + 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}