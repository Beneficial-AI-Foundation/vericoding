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
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
        forall|i: int, j: int| 0 <= i < j < nums.len() && i < result.0 as int ==> nums[i] + nums[j] != target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clauses to both loops */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            nums.len() > 1,
            i <= nums.len(),
            exists|i_ex: int, j_ex: int| 0 <= i_ex < j_ex < nums.len() && nums@[i_ex] + nums@[j_ex] == target,
            forall|x: int, y: int| 0 <= x < y < nums.len() && x < i as int ==> nums@[x] + nums@[y] != target,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                nums.len() > 1,
                i < nums.len(),
                j <= nums.len(),
                exists|i_ex: int, j_ex: int| 0 <= i_ex < j_ex < nums.len() && nums@[i_ex] + nums@[j_ex] == target,
                forall|x: int, y: int| 0 <= x < y < nums.len() && x < i as int ==> nums@[x] + nums@[y] != target,
                forall|y: int| i as int + 1 <= y < j as int ==> nums@[i as int] + nums@[y] != target,
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}