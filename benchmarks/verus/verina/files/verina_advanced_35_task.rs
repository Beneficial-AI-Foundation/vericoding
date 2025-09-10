/* This task requires writing a Verus function that finds the majority element in a sequence of integers. The majority element is the element that appears more than ⌊n/2⌋ times, where n is the sequence's length. You may assume that a majority element always exists in the input.

-----Input-----
- nums: A sequence of integers of length ≥ 1, containing a majority element.

-----Output-----
- An integer: the element that appears more than ⌊n/2⌋ times. */

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
fn majority_element(nums: Seq<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|x: i32| count_occurrences(nums, x) > nums.len() / 2,
    ensures 
        count_occurrences(nums, result) > nums.len() / 2,
        forall|x: i32| x != result ==> count_occurrences(nums, x) <= nums.len() / 2,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}