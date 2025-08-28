use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemmas for two_sum verification
proof fn lemma_solution_exists(nums: &[i32], target: i32)
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
{
    // This lemma preserves the existence property
}

proof fn lemma_nested_loop_completeness(nums: &[i32], target: i32, outer_bound: int)
    requires
        nums.len() >= 2,
        0 <= outer_bound <= nums.len(),
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int| 0 <= i < outer_bound && i < j < nums.len() ==> nums[i] + nums[j] != target,
    ensures
        exists|i: int, j: int| outer_bound <= i < j < nums.len() && nums[i] + nums[j] == target,
{
    // Proves that if no solution exists in searched pairs, solution must be in remaining pairs
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
    // impl-start
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target,
            forall|x: int, y: int|
                0 <= x < nums.len() && 0 <= y < nums.len()
                    ==> nums[x] + nums[y] <= i32::MAX
                        && nums[x] + nums[y] >= i32::MIN,
            forall|x: int, y: int| 0 <= x < i && x < y < nums.len() ==> nums[x] + nums[y] != target,
        decreases nums.len() - i
    {
        proof {
            lemma_nested_loop_completeness(nums, target, i as int);
        }
        
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target,
                forall|x: int, y: int|
                    0 <= x < nums.len() && 0 <= y < nums.len()
                        ==> nums[x] + nums[y] <= i32::MAX
                            && nums[x] + nums[y] >= i32::MIN,
                forall|k: int| i + 1 <= k < j ==> nums[i as int] + nums[k] != target,
                forall|x: int, y: int| 0 <= x < i && x < y < nums.len() ==> nums[x] + nums[y] != target,
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(i == nums.len());
        assert(forall|x: int, y: int| 0 <= x < i && x < y < nums.len() ==> nums[x] + nums[y] != target);
        assert(forall|x: int, y: int| 0 <= x < nums.len() && x < y < nums.len() ==> nums[x] + nums[y] != target);
        assert(exists|x: int, y: int| 0 <= x < y < nums.len() && nums[x] + nums[y] == target);
        assert(false);
    }
    unreached()
    // impl-end
}
// </vc-code>

fn main() {}
}