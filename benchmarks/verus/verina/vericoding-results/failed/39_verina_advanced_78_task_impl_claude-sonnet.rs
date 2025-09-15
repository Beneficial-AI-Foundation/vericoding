// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof logic to convert between int and usize indices */
spec fn valid_pair(nums: &Vec<i32>, i: usize, j: usize, target: i32) -> bool {
    i < j && i < nums.len() && j < nums.len() && nums[i as int] + nums[j as int] == target
}

proof fn pair_exists_lemma(nums: &Vec<i32>, target: i32)
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        exists|i: usize, j: usize| valid_pair(nums, i, j, target)
{
    proof {
        let witness_pair = choose|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target;
        let i_usize = witness_pair.0 as usize;
        let j_usize = witness_pair.1 as usize;
        assert(valid_pair(nums, i_usize, j_usize, target));
    }
}
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
    /* code modified by LLM (iteration 5): fixed ghost type usage by moving assertions to proof blocks */
    proof { pair_exists_lemma(nums, target); }
    
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|x: usize, y: usize| x < i && y < nums.len() && x < y ==> nums[x as int] + nums[y as int] != target,
            exists|a: usize, b: usize| valid_pair(nums, a, b, target),
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall|x: usize, y: usize| x < i && y < nums.len() && x < y ==> nums[x as int] + nums[y as int] != target,
                forall|y: usize| i + 1 <= y < j ==> nums[i as int] + nums[y as int] != target,
                exists|a: usize, b: usize| valid_pair(nums, a, b, target),
            decreases nums.len() - j
        {
            let sum = nums[i] + nums[j];
            if sum == target {
                proof {
                    assert(nums[i as int] + nums[j as int] == target);
                    assert(valid_pair(nums, i, j, target));
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