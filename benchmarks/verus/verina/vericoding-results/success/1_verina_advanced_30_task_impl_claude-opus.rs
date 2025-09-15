// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed type mismatches in helper functions */
spec fn is_increasing_at(nums: &Vec<i32>, i: usize) -> bool
    recommends i + 1 < nums.len()
{
    nums[i as int] < nums[(i + 1) as int]
}

spec fn streak_len_from(nums: &Vec<i32>, start: usize, end: usize) -> nat
    recommends start <= end && end <= nums.len()
    decreases end - start
{
    if start >= end || start + 1 >= end {
        if start < end { 1 } else { 0 }
    } else if start + 1 < nums.len() && is_increasing_at(nums, start) {
        1 + streak_len_from(nums, (start + 1) as usize, end)
    } else {
        1
    }
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_streak(nums: &Vec<i32>) -> (result: usize)
    ensures
        (nums.len() == 0 ==> result == 0),
        result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
    if nums.len() == 0 {
        return 0;
    }
    
    let mut max_streak: usize = 1;
    let mut current_streak: usize = 1;
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            current_streak >= 1,
            max_streak >= 1,
            max_streak <= i,
            current_streak <= i,
        decreases nums.len() - i
    {
        if nums[i - 1] < nums[i] {
            current_streak = current_streak + 1;
            if current_streak > max_streak {
                max_streak = current_streak;
            }
        } else {
            current_streak = 1;
        }
        i = i + 1;
    }
    
    max_streak
}
// </vc-code>

}
fn main() {}