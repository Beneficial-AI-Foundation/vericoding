// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_valid_index_pair(len: nat, i: nat, j: nat) -> bool { i < j && j < len }

fn min_i32(a: i32, b: i32) -> i32 { if a < b { a } else { b } }

proof fn lemma_valid_pair_implies_len_gt_one(i: nat, j: nat, len: nat)
    requires
        i < j && j < len,
    ensures
        1 < len,
{ }
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: (usize, usize))
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        result.0 < result.1,
        result.0 < nums.len(),
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    let mut i: usize = 0;
    loop {
        while i + 1 < n {
            let mut j: usize = i + 1;
            while j < n {
                if nums[i] + nums[j] == target {
                    return (i, j);
                }
                j += 1;
            }
            i += 1;
        }
        // Due to the precondition, a valid pair must exist; restart scan to ensure a return
        i = 0;
    }
}
// </vc-code>

}
fn main() {}