// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, value: i32) -> nat {
    nums.filter(|x: i32| x == value).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): argmax_idx returns index of a most frequent element */
spec fn argmax_idx(nums: Seq<i32>) -> (r: nat)
    requires nums.len() > 0,
    ensures
        r < nums.len(),
        forall|j: nat| j < nums.len() ==> count_occurrences(nums, nums.index(r)) >= count_occurrences(nums, nums.index(j)),
{
    choose |i: nat| i < nums.len() && forall|j: nat| j < nums.len() ==> count_occurrences(nums, nums.index(i)) >= count_occurrences(nums, nums.index(j))
}

/* helper modified by LLM (iteration 5): most_frequent returns element with maximal occurrences */
spec fn most_frequent(nums: Seq<i32>) -> (r: i32)
    requires nums.len() > 0,
    ensures
        forall|x: i32| count_occurrences(nums, r) >= count_occurrences(nums, x),
{
    nums.index(argmax_idx(nums))
}
// </vc-helpers>

// <vc-spec>
fn majority_element(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures ({
        let nums_seq = nums@;
        let n = nums_seq.len();
        count_occurrences(nums_seq, result) > n / 2 &&
        forall|x: i32| x == result || count_occurrences(nums_seq, x) <= n / 2
    }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return the most frequent element using helpers */
    let nums_seq = nums@;
    let res = most_frequent(nums_seq);
    res
}
// </vc-code>

}
fn main() {}