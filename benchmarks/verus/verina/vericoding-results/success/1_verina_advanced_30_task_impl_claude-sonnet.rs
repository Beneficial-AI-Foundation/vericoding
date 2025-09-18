// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


// </vc-helpers>

// <vc-spec>
fn longest_increasing_streak(nums: &Vec<i32>) -> (result: usize)
    ensures
        (nums.len() == 0 ==> result == 0),
        result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed invariants and overflow issues */
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
        if nums[i] > nums[i - 1] {
            current_streak = current_streak + 1;
        } else {
            current_streak = 1;
        }
        
        if current_streak > max_streak {
            max_streak = current_streak;
        }
        
        i = i + 1;
    }
    
    max_streak
}
// </vc-code>

}
fn main() {}