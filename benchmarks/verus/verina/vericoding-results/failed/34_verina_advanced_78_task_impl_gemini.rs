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
    /* code modified by LLM (iteration 5): remove semicolon from unreached() to make it the return expression */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= (i as int) <= nums.len(),
            forall|x: int, y: int| 0 <= x < (i as int) && x < y < nums.len() ==> nums[x] + nums[y] != target,
        decreases nums.len() - i as int,
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= (i as int) < nums.len(),
                (i as int) < (j as int) <= nums.len(),
                forall|x: int, y: int| 0 <= x < (i as int) && x < y < nums.len() ==> nums[x] + nums[y] != target,
                forall|k: int| (i as int) < k < (j as int) ==> nums[i as int] + nums[k] != target,
            decreases nums.len() - j as int,
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