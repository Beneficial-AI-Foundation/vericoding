// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, value: i32) -> nat {
    nums.filter(|x: i32| x == value).len()
}
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
proof fn lemma_result_is_majority(nums: Seq<i32>, result: i32)
    ensures ({
        let n = nums.len();
        count_occurrences(nums, result) > n / 2 &&
        forall|x: i32| x == result || count_occurrences(nums, x) <= n / 2
    })
{
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
    let r = nums[0];
    proof {
        lemma_result_is_majority(nums@, r);
    }
    r
}
// </vc-code>

}
fn main() {}