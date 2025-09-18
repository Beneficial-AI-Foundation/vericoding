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
    /* code modified by LLM (iteration 5): [Fixed type errors related to `int` and `nat` and sequence indexing.] */
    let n = nums.len();
    let mut candidate: i32 = nums[0];
    let mut count: int = 0;

    let mut i: int = 0;
    while i < n as int
        invariant
            0 <= i <= n as int,
        decreases (n - i) as nat
    {
        if count == 0 {
            candidate = nums.view_nth(i as nat);
            count = 1;
        } else if nums.view_nth(i as nat) == candidate {
            count = count + 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    candidate
}
// </vc-code>

}
fn main() {}