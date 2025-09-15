// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max(a: usize, b: usize) -> (c: usize)
    ensures c == a || c == b, c >= a, c >= b
{
    if a > b {a} else {b}
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
    if nums.len() == 0 {
        return 0;
    }

    let mut max_streak: usize = 1;
    let mut current_streak: usize = 1;
    let mut i: usize = 1;

    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            1 <= current_streak,
            current_streak <= i,
            1 <= max_streak,
            max_streak <= nums.len(),
        decreases nums.len() - i
    {
        if nums[i] > nums[i - 1] {
            current_streak = current_streak + 1;
        } else {
            current_streak = 1;
        }

        max_streak = max(max_streak, current_streak);
        
        i = i + 1;
    }

    max_streak
}
// </vc-code>

}
fn main() {}