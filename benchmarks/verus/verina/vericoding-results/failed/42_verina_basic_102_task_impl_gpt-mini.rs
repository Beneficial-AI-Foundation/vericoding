// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): convert usize to int */
fn usize_to_int(n: usize) -> int {
    n as int
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
    /* code modified by LLM (iteration 2): implement two-sum with int-indexed loops and invariants */
    let n = nums.len();
    let n_int: int = n as int;

    let (iw, jw) = choose |i: int, j: int| 0 <= i < j < n_int && nums[i as usize] + nums[j as usize] == target;
    let iw_u: usize = iw as usize;
    let jw_u: usize = jw as usize;

    let mut i: int = 0;
    while i < n_int - 1
        invariant
            0 <= i && i <= n_int,
            forall|k: int, l: int| 0 <= k < l < n_int && k < i ==> nums[k as usize] + nums[l as usize] != target,
        decreases n_int - i
    {
        let mut j: int = i + 1;
        while j < n_int
            invariant
                i < n_int,
                i + 1 <= j && j <= n_int,
                forall|l: int| i < l < j ==> nums[i as usize] + nums[l as usize] != target,
            decreases n_int - j
        {
            if nums[i as usize] + nums[j as usize] == target {
                return (i as usize, j as usize);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    (iw_u, jw_u)
}
// </vc-code>

}
fn main() {}