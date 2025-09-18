// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to prove no earlier pairs sum to target */
lemma sum_not_found_lemma(nums: &Vec<i32>, target: i32, found_i: usize, found_j: usize)
    requires
        found_i < found_j,
        found_j < nums.len(),
        nums[found_i as int] + nums[found_j as int] == target,
        forall|x: int, y: int| 0 <= x < y < nums.len() && x < found_i ==> nums[x] + nums[y] != target,
    ensures
        forall|i: int, j: int| 0 <= i < j < nums.len() && i < found_i as int ==> nums[i] + nums[j] != target,
{
}
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
    /* code modified by LLM (iteration 5): added proof block with lemma call to establish postcondition */
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|x: int, y: int| 0 <= x < y < nums.len() && x < i ==> nums[x] + nums[y] != target,
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i + 1 <= j <= nums.len(),
                forall|y: int| i + 1 <= y < j ==> nums[i as int] + nums[y] != target,
            decreases nums.len() - j
        {
            let sum = nums[i] as i64 + nums[j] as i64;
            if sum == target as i64 {
                proof {
                    sum_not_found_lemma(nums, target, i, j);
                }
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}