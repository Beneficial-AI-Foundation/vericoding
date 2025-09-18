// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize index to int with bounds */
spec fn usize_to_int(i: usize, n: usize) -> int
    requires
        i < n,
    ensures
        result == i as int && 0 <= result && result < n as int,
{
    i as int
}
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
    /* code modified by LLM (iteration 5): nested loops using usize indexing and seq specs */
    let n: usize = nums.len();
    let mut i: usize = 0usize;
    while i < n
        invariant
            forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && k1 < i as int ==> nums@[k1] + nums@[k2] != target,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && (k1 < i as int || (k1 == i as int && k2 < j as int)) ==> nums@[k1] + nums@[k2] != target,
            decreases n - j
        {
            if nums[i] + nums[j] == target {
                return Some((i, j));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    None
}
// </vc-code>

}
fn main() {}