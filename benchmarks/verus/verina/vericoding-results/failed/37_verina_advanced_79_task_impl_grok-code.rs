// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): No changes needed, helper is correct */
spec fn no_two_sum_in_range(nums: Seq<i32>, target: i32, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i < j < end ==> nums[i] + nums[j] != target
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

/* code modified by LLM (iteration 5): Removed parentheses from while loop conditions to fix compilation error */
{
    let len = nums@.len();
    let mut i: usize = 0;
    while i < len
        invariant no_two_sum_in_range(nums@, target, 0, i as int);
    {
        let mut j: usize = i + 1;
        while j < len
            invariant no_two_sum_in_range(nums@, target, 0, (i + 1) as int);
            invariant forall|k: int| (i as int) < k < (j as int) ==> nums@[i as int] + nums@[k] != target;
        {
            if nums@[i as int] + nums@[j as int] == target {
                return Some((i, j));
            }
            j += 1;
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}