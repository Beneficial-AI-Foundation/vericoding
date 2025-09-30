// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No helpers needed */
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
/* code modified by LLM (iteration 4): Corrected loop invariants and postcondition to handle potential overflows and improve verification. */
{
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i && i <= nums.len(),
            forall|k1: int, k2: int| 0 <= k1 < i && k1 < k2 && k2 < nums.len() ==> nums[k1] + nums[k2] != target,
        decreases (nums.len() - i) as int
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < j && j <= nums.len(),
                forall|k1: int, k2: int| ((0 <= k1 < i && k1 < k2 && k2 < nums.len()) || (k1 == i && i < k2 < j)) ==> nums[k1] + nums[k2] != target,
            decreases (nums.len() - j) as int
        {
            if nums[i].checked_add(nums[j]).is_some() && nums[i] + nums[j] == target {
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