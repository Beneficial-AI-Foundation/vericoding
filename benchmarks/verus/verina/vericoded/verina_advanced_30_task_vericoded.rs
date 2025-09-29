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
    /* code modified by LLM (iteration 3): fixed arithmetic overflow and loop invariant maintenance */
    if nums.len() == 0 {
        return 0;
    }
    
    let mut max_streak = 1;
    let mut current_streak = 1;
    let mut i = 1;
    
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            current_streak >= 1,
            max_streak >= 1,
            max_streak <= nums.len(),
            current_streak <= i,
        decreases nums.len() - i
    {
        if nums[i] > nums[i - 1] {
            proof {
                assert(current_streak < nums.len());
            }
            current_streak += 1;
        } else {
            current_streak = 1;
        }
        
        if current_streak > max_streak {
            max_streak = current_streak;
        }
        
        i += 1;
    }
    
    max_streak
}
// </vc-code>

}
fn main() {}