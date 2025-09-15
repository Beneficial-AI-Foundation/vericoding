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
    /* code modified by LLM (iteration 4): Added missing comma in inner loop invariant. */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|k1: int, k2: int|
                0 <= k1 < i as int && k1 < k2 && k2 < nums.len() as int ==> 
                nums[k1] + nums[k2] != target,
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i < j <= nums.len(),
                forall|k1: int, k2: int| 
                    0 <= k1 < i as int && k1 < k2 && k2 < nums.len() as int ==> 
                    nums[k1] + nums[k2] != target,
                forall|k2: int| 
                    i as int < k2 && k2 < j as int ==> 
                    nums[i as int] + nums[k2] != target,
        {
            if nums[i] + nums[j] == target {
                return Some((i, j));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return None;
}
// </vc-code>

}
fn main() {}