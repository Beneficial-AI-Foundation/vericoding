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
    /* code modified by LLM (iteration 3): Added overflow check and strengthened invariants */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < nums.len() && k1 < k2 ==> nums[k1] + nums[k2] != target,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < nums.len() && k1 < k2 ==> nums[k1] + nums[k2] != target,
                forall|k2: int| i + 1 <= k2 < j ==> nums[i as int] + nums[k2] != target,
            decreases nums.len() - j
        {
            if nums[i] as i64 + nums[j] as i64 == target as i64 {
                return Some((i, j));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert(forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 != k2 ==> nums[k1] + nums[k2] != target) by {
            assert(forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 ==> nums[k1] + nums[k2] != target);
        };
    }
    None
}
// </vc-code>

}
fn main() {}