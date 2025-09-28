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
{
    /* code modified by LLM (iteration 5): implement Boyer-Moore algorithm, cast len to int for proper typing in Verus */
    let len = nums.len() as int;
    let mut candidate = nums[0];
    let mut count = 1i32;
    let mut i = 1;
    while i < len
        invariant
            0 < i <= len,
            1 <= count <= i,
        decreases len - i
    {
        if nums[i] == candidate {
            count += 1;
        } else {
            count -= 1;
            if count == 0 {
                candidate = nums[i];
                count = 1;
            }
        }
        i += 1;
    }
    candidate
}
// </vc-code>

}
fn main() {}