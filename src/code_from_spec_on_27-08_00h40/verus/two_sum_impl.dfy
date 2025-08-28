use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_solution_at(nums: &[i32], target: i32, i: int, j: int) -> bool {
    0 <= i < j < nums.len() && nums[i] + nums[j] == target
}

spec fn has_solution_before(nums: &[i32], target: i32, bound: int) -> bool {
    exists|i: int, j: int| i < bound && has_solution_at(nums, target, i, j)
}

proof fn solution_exists_lemma(nums: &[i32], target: i32)
    requires
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        has_solution_before(nums, target, nums.len() as int),
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    // pre-conditions-start
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    proof {
        solution_exists_lemma(nums, target);
    }
    
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            has_solution_before(nums, target, nums.len() as int),
            forall|k: int, l: int|
                0 <= k < i && 0 <= l < nums.len() && k != l
                    ==> nums[k] + nums[l] != target,
        decreases nums.len() - i,
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                has_solution_before(nums, target, nums.len() as int),
                forall|k: int, l: int|
                    0 <= k < i && 0 <= l < nums.len() && k != l
                        ==> nums[k] + nums[l] != target,
                forall|l: int|
                    i + 1 <= l < j
                        ==> nums[i as int] + nums[l] != target,
            decreases nums.len() - j,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    
    unreached()
}
// </vc-code>

fn main() {}
}