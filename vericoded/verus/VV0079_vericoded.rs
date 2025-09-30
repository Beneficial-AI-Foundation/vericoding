// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: Vec<usize>)
    requires 
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= j < i < nums.len() && nums[i] + nums[j] == target,
        forall|i1: int, j1: int, i2: int, j2: int| 
            (0 <= j1 < i1 < nums.len() && nums[i1] + nums[j1] == target &&
             0 <= j2 < i2 < nums.len() && nums[i2] + nums[j2] == target) ==> 
            (i1 == i2 && j1 == j2),
    ensures
        result.len() == 2,
        result[0] < nums.len(),
        result[1] < nums.len(),
        result[0] < result[1],
        nums[result[0] as int] + nums[result[1] as int] == target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow with checked addition */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|i_prev: int, j_prev: int| 0 <= j_prev < i_prev < i ==> nums[i_prev] + nums[j_prev] != target,
        decreases nums.len() - i
    {
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i,
                i < nums.len(),
                forall|j_prev: int| 0 <= j_prev < j ==> nums[i as int] + nums[j_prev] != target,
            decreases i - j
        {
            let sum = nums[i] as i64 + nums[j] as i64;
            if sum == target as i64 {
                let mut result = Vec::new();
                result.push(j);
                result.push(i);
                assert(result.len() == 2);
                assert(result[0] == j);
                assert(result[1] == i);
                assert(j < i);
                assert(nums[j as int] + nums[i as int] == target);
                return result;
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