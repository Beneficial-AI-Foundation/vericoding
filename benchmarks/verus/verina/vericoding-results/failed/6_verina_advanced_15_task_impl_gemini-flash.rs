// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed the helper function as it was not used and the main logic can be implemented directly. */
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
/* code modified by LLM (iteration 5): Corrected `usize` to `int` casts for array indexing within `exists` clauses to satisfy spec type checking. */
{
    let mut smallest_so_far: i32 = 0x7fffffff;
    let mut second_smallest: i32 = 0x7fffffff;

    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i && i <= nums.len(),
            smallest_so_far == 0x7fffffff || (exists|s_idx: int| 0 <= s_idx < i as int && smallest_so_far == nums.reveal_value().into_raw_slice()[s_idx as usize]),
            second_smallest == 0x7fffffff || (exists|s1_idx: int, s2_idx: int| 0 <= s1_idx < s2_idx && s2_idx < i as int && nums.reveal_value().into_raw_slice()[s1_idx as usize] < nums.reveal_value().into_raw_slice()[s2_idx as usize] && second_smallest == nums.reveal_value().into_raw_slice()[s2_idx as usize]),
            (second_smallest != 0x7fffffff) ==> (smallest_so_far < second_smallest)
        decreases nums.len() - i
    {
        let val = nums[i];
        if val <= smallest_so_far {
            smallest_so_far = val;
        } else if val <= second_smallest {
            second_smallest = val;
        } else {
            // Found a triplet: smallest_so_far < second_smallest < val
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}