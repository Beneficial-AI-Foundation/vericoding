// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn two_sum(nums: Vec<i32>, target: i32) -> (result: Option<(usize, usize)>)
    ensures
        match result {
            None => {
                forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j] != target
            },
            Some((i, j)) => {
                i < j &&
                j < nums.len() &&
                nums[i as int] + nums[j as int] == target &&
                forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added proper bounds checks for array indexing */
    let n = nums.len();
    for i in 0..n
        invariant
            forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < n && k1 < k2 ==> nums[k1] + nums[k2] != target
    {
        for j in (i + 1)..n
            invariant
                i < n,
                forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < n && k1 < k2 ==> nums[k1] + nums[k2] != target,
                forall|k2: int| i + 1 <= k2 < j ==> nums[i as int] + nums[k2] != target
        {
            if nums[i as int] + nums[j as int] == target {
                return Some((i, j));
            }
        }
    }
    None
}
// </vc-code>

}
fn main() {}