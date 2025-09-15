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
/* code modified by LLM (iteration 5): Corrected type casting within loop invariants. */
{
    let n = nums.len();

    if n == 0 {
        return Option::None;
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            forall|k1: int, k2: int|
                0 <= k1 < i as int && 0 <= k2 < n as int && k1 < k2
                ==>
                nums[k1] + nums[k2] != target,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                (i as int) < (j as int) <= n as int,
                forall|k1: int, k2: int|
                    (0 <= k1 < i as int && 0 <= k2 < n as int && k1 < k2)
                    ||
                    (k1 == i as int && 0 <= k2 < j as int && k1 < k2)
                    ==>
                    nums[k1] + nums[k2] != target,
        {
            if nums[i] + nums[j] == target {
                return Option::Some((i, j));
            }
            j = j + 1;
        }
        i = i + 1;
    }

    Option::None
}
// </vc-code>

}
fn main() {}