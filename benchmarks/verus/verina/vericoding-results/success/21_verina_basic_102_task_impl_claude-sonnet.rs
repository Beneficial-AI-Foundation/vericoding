// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added safe_add function to handle overflow */
spec fn safe_add(a: i32, b: i32) -> bool {
    let sum = a as i64 + b as i64;
    sum >= i32::MIN as i64 && sum <= i32::MAX as i64
}

proof fn exists_solution_lemma(nums: &Vec<i32>, target: i32)
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        exists|i: usize, j: usize| i < j && (j as int) < nums.len() && nums[i as int] + nums[j as int] == target
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
    /* code modified by LLM (iteration 4): fixed overflow and postcondition with proper bounds checking */
    let mut i = 0;
    while i < nums.len() - 1
        invariant
            i <= nums.len() - 1,
            forall|x: int, y: int| 0 <= x < y < nums.len() && x < i ==> nums[x] + nums[y] != target,
            exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target,
        decreases nums.len() - 1 - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i < nums.len() - 1,
                j <= nums.len(),
                i + 1 <= j,
                forall|x: int, y: int| 0 <= x < y < nums.len() && x < i ==> nums[x] + nums[y] != target,
                forall|y: int| (i as int) < y < (j as int) ==> nums[i as int] + nums[y] != target,
                exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target,
            decreases nums.len() - j
        {
            let a = nums[i];
            let b = nums[j];
            let sum = a as i64 + b as i64;
            if sum == target as i64 {
                proof {
                    assert(i < j);
                    assert(j < nums.len());
                    assert(nums[i as int] + nums[j as int] == target);
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