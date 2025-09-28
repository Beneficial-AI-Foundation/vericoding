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
    /* code modified by LLM (iteration 5): Fixed type error by casting i to int in assertion */
    if nums.len() < 3 {
        return false;
    }
    
    let mut first = i32::MAX;
    let mut second = i32::MAX;
    let mut i = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            first == i32::MAX || (exists|j: int| 0 <= j < i && nums[j] <= first),
            second == i32::MAX || (first < second && exists|j1: int, j2: int| 0 <= j1 < j2 && j2 < i && nums[j1] < nums[j2] && nums[j2] <= second),
            forall|j1: int, j2: int, j3: int| 0 <= j1 < j2 && j2 < j3 && j3 < i ==> !(nums[j1] < nums[j2] && nums[j2] < nums[j3]),
            first != i32::MAX ==> forall|j: int| 0 <= j < i ==> nums[j] >= first,
            second != i32::MAX ==> first < second,
        decreases nums.len() - i
    {
        if nums[i] <= first {
            first = nums[i];
        } else if nums[i] <= second {
            // nums[i] > first && nums[i] <= second
            second = nums[i];
        } else {
            // nums[i] > second && second > first
            // This means we found an increasing triplet
            assert(first < second);
            assert(second < nums[i as int]);
            assert(exists|j1: int, j2: int| 0 <= j1 < j2 && j2 < i && nums[j1] < nums[j2] && nums[j2] <= second);
            return true;
        }
        i = i + 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}