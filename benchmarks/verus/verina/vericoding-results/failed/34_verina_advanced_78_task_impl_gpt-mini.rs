// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): vector length as int */
spec fn vec_len_int<T>(v: &Vec<T>) -> int { v.len() as int }

/* helper modified by LLM (iteration 5): convert usize to int for specs */
spec fn usize_to_int(u: usize) -> int { u as int }
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
    /* code modified by LLM (iteration 5): search using usize indices and spec casts */
    let n = nums.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|i0: int, j0: int| 0 <= i0 && i0 < (i as int) && i0 < j0 && j0 < (n as int) ==> nums[i0 as usize] + nums[j0 as usize] != target,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < n,
                j <= n,
                forall|i0: int, j0: int| 0 <= i0 && i0 < (i as int) && i0 < j0 && j0 < (n as int) ==> nums[i0 as usize] + nums[j0 as usize] != target,
            decreases n - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert(exists|i0: int, j0: int| 0 <= i0 < j0 && j0 < (n as int) && nums[i0 as usize] + nums[j0 as usize] == target);
        assert(forall|i0: int, j0: int| 0 <= i0 && i0 < (n as int) && i0 < j0 && j0 < (n as int) ==> nums[i0 as usize] + nums[j0 as usize] != target);
        assert(false);
    }
    unreached()
}
// </vc-code>

}
fn main() {}