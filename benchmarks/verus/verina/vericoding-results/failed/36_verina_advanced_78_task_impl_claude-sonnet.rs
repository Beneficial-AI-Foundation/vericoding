// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn has_solution(nums: &Vec<i32>, target: i32) -> bool {
    exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target
}

/* helper modified by LLM (iteration 5): strengthened lemma to prove solution preservation */
proof fn solution_exists_implies_findable(nums: &Vec<i32>, target: i32, i: usize)
    requires
        has_solution(nums, target),
        i < nums.len(),
        forall|x: int, y: int| 0 <= x < i && x < y < nums.len() ==> nums[x] + nums[y] != target
    ensures
        exists|x: int, y: int| i <= x < y < nums.len() && nums[x] + nums[y] == target
{
    proof {
        let (a, b) = choose|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target;
        if a >= i {
            assert(i <= a < b < nums.len() && nums[a] + nums[b] == target);
        } else {
            assert(false); // contradiction with forall condition
        }
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
    /* code modified by LLM (iteration 5): fixed overflow check and proof obligations */
    let mut i = 0;
    while i < nums.len() - 1
        invariant
            i <= nums.len(),
            exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target,
            forall|x: int, y: int| 0 <= x < i && x < y < nums.len() ==> nums[x] + nums[y] != target
        decreases nums.len() - i
    {
        solution_exists_implies_findable(nums, target, i);
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                j <= nums.len(),
                i + 1 <= j,
                exists|x: int, y: int| i <= x < y < nums.len() && nums[x] + nums[y] == target,
                forall|k: int| i + 1 <= k < j ==> nums[i as int] + nums[k] != target
            decreases nums.len() - j
        {
            if nums[i as int] >= i32::MIN / 2 && nums[j as int] >= i32::MIN / 2 &&
               nums[i as int] <= i32::MAX / 2 && nums[j as int] <= i32::MAX / 2 {
                if nums[i] + nums[j] == target {
                    assert(i < j);
                    assert(i < nums.len() && j < nums.len());
                    assert(nums[i as int] + nums[j as int] == target);
                    return (i, j);
                }
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