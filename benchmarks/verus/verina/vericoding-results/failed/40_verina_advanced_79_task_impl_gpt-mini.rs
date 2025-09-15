// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec for valid index */
spec fn is_valid_index(len: int, i: int) -> bool { 0 <= i && i < len }

/* helper modified by LLM (iteration 5): commutativity of addition */
proof fn add_comm(a: i32, b: i32) ensures a + b == b + a { proof { assert(a + b == b + a); } }
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
    /* code modified by LLM (iteration 5): iterative two-sum search using usize indices with decreases for termination; minimal invariants removed to fix parsing */
    let n: usize = nums.len();
    let mut i: usize = 0;
    while i < n
        decreases n - i;
    {
        let mut j: usize = i + 1;
        while j < n
            decreases n - j;
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