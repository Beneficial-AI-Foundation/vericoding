// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed sequence access bounds and added proper proof reasoning */
    let n = nums.len();
    for i in 0..n
        invariant
            forall|i_prev: int, j_prev: int| 0 <= i_prev < i && i_prev < j_prev < n ==> nums@[i_prev] + nums@[j_prev] != target,
            exists|i_exist: int, j_exist: int| 0 <= i_exist < j_exist < n && nums@[i_exist] + nums@[j_exist] == target,
    {
        for j in (i + 1)..n
            invariant
                i < n,
                j >= i + 1,
                j <= n,
                forall|j_prev: int| i + 1 <= j_prev < j ==> nums@[i as int] + nums@[j_prev] != target,
                forall|i_prev: int, j_prev: int| 0 <= i_prev < i && i_prev < j_prev < n ==> nums@[i_prev] + nums@[j_prev] != target,
                exists|i_exist: int, j_exist: int| 0 <= i_exist < j_exist < n && nums@[i_exist] + nums@[j_exist] == target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
        }
    }
    unreached()
}
// </vc-code>

}
fn main() {}