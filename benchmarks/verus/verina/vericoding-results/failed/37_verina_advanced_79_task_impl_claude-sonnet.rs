// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed to exec mode helper function to check if addition is safe */
fn add_i32_no_overflow(a: i32, b: i32) -> (result: bool)
    ensures result == (a <= i32::MAX - b && a >= i32::MIN - b)
{
    if a >= 0 {
        a <= i32::MAX - b
    } else {
        a >= i32::MIN - b
    }
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
    /* code modified by LLM (iteration 5): using exec mode helper function */
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|k1: int, k2: int| 0 <= k1 < i && k1 < k2 < nums.len() ==> nums[k1] + nums[k2] != target,
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall|k1: int, k2: int| 0 <= k1 < i && k1 < k2 < nums.len() ==> nums[k1] + nums[k2] != target,
                forall|k2: int| i + 1 <= k2 < j ==> nums[i as int] + nums[k2] != target,
            decreases nums.len() - j
        {
            if add_i32_no_overflow(nums[i], nums[j]) && nums[i] + nums[j] == target {
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