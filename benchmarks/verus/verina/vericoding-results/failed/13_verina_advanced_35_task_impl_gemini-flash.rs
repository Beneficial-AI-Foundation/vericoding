// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat 
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else {
        let first = nums[0];
        let rest_count = count_occurrences(nums.subrange(1, nums.len() as int), x);
        if first == x {
            rest_count + 1
        } else {
            rest_count
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed requires/ensures from spec function `get_majority_element_recursive` to fix compilation error. */
spec fn get_majority_element_recursive(nums: Seq<i32>) -> (result: i32)
{
    if nums.len() == 1 {
        nums[0]
    } else {
        let mid = nums.len() / 2;
        let left_half = nums.subrange(0, mid as int);
        let right_half = nums.subrange(mid as int, nums.len() as int);

        let major_left = if left_half.len() > 0 && exists|x: i32| count_occurrences(left_half, x as i32) > (left_half.len() as nat) / 2 {
            get_majority_element_recursive(left_half)
        } else {
            nums[0]
        };
        let major_right = if right_half.len() > 0 && exists|x: i32| count_occurrences(right_half, x as i32) > (right_half.len() as nat) / 2 {
            get_majority_element_recursive(right_half)
        } else {
            nums[0]
        };

        let count_left = count_occurrences(nums, major_left);
        let count_right = count_occurrences(nums, major_right);

        if count_left > (nums.len() as nat) / 2 {
            major_left
        } else if count_right > (nums.len() as nat) / 2 {
            major_right
        } else {
            nums[0]
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn majority_element(nums: Seq<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|x: i32| count_occurrences(nums, x) > nums.len() / 2,
    ensures 
        count_occurrences(nums, result) > nums.len() / 2,
        forall|x: i32| x != result ==> count_occurrences(nums, x) <= nums.len() / 2,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calling recursive majority element helper */
{
    get_majority_element_recursive(nums)
}
// </vc-code>

}
fn main() {}