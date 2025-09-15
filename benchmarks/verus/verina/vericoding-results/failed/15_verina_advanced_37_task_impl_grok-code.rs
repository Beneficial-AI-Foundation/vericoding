// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, value: i32) -> nat {
    nums.filter(|x: i32| x == value).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed placement of ensures keyword in proof fn and ensured proof body establishes the ensures */
spec fn helper_count(nums: Seq<i32>, val: i32) -> nat {
    nums.filter(|x: i32| x == val).len()
}
proof fn lemma_helper(nums: Seq<i32>, val: i32)
    ensures count_occurrences(nums, val) == helper_count(nums, val);
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
/* code modified by LLM (iteration 5): Implemented Boyer-Moore majority vote algorithm with second pass to verify majority condition */
{
    let nums_seq = nums@;
    let n = nums_seq.len();
    let mut candidate = nums_seq[0];
    let mut count = 1;
    let mut i = 1;
    while i < n
        invariant
            1 <= i <= n,
            1 <= count <= i + 1
    {
        if nums_seq[i] == candidate {
            count += 1;
        } else {
            count -= 1;
            if count == 0 {
                candidate = nums_seq[i];
                count = 1;
            }
        }
        i += 1;
    }
    // Second pass to verify majority
    let mut actual_count = 0;
    let mut j = 0;
    while j < n {
        if nums_seq[j] == candidate {
            actual_count += 1;
        }
        j += 1;
    }
    assert(actual_count > n / 2);
    candidate
}

// </vc-code>

}
fn main() {}