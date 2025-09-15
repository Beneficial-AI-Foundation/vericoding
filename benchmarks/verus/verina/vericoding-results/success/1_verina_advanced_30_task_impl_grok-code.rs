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
    /* code modified by LLM (iteration 4): added missing invariant clause for max_streak <= nums.len() to ensure postcondition */
    if nums.len() == 0 {
        return 0;
    }
    let mut max_streak: usize = 1;
    let mut curr_streak: usize = 1;
    let mut prev: i32 = nums[0];
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            0 < i <= nums.len(),
            1 <= curr_streak,
            curr_streak <= i,
            max_streak >= curr_streak,
            max_streak >= 1,
            max_streak <= nums.len(),
        decreases nums.len() - i
    {
        if nums[i] > prev {
            curr_streak = curr_streak + 1;
            if curr_streak > max_streak {
                max_streak = curr_streak;
            }
        } else {
            curr_streak = 1;
        }
        prev = nums[i];
        i = i + 1;
    }
    assert(max_streak <= nums.len());
    max_streak
}
// </vc-code>

}
fn main() {}