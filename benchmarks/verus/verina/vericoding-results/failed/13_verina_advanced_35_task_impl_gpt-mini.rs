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
/* helper modified by LLM (iteration 5): predicate for majority */
spec fn is_majority(nums: Seq<i32>, x: i32) -> bool { count_occurrences(nums, x) * 2 > nums.len() }

/* helper modified by LLM (iteration 5): choose a majority witness when one exists */
proof fn choose_majority_witness(nums: Seq<i32>) requires exists|x: i32| count_occurrences(nums, x) * 2 > nums.len() ensures exists|m: i32| count_occurrences(nums, m) * 2 > nums.len() {
    proof {
        let m = choose|v: i32| count_occurrences(nums, v) * 2 > nums.len();
        assert(count_occurrences(nums, m) * 2 > nums.len());
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
{
    /* code modified by LLM (iteration 5): select majority element using spec-level choice */
    let result: i32 = choose|v: i32| count_occurrences(nums, v) * 2 > nums.len();
    result
}
// </vc-code>

}
fn main() {}