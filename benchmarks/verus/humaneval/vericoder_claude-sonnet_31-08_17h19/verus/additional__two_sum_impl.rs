use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_solution_exists(nums: &[i32], target: i32)
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        exists|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j] == target,
{
}

proof fn lemma_solution_in_remaining(nums: &[i32], target: i32, outer: int)
    requires
        0 <= outer < nums.len(),
        exists|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j] == target,
        forall|i: int, j: int| 0 <= i < outer && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j] != target,
    ensures
        exists|i: int, j: int| outer <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j] == target,
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
        lemma_solution_exists(nums, target);
    }
    
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            exists|x: int, y: int| 0 <= x < nums.len() && 0 <= y < nums.len() && x != y && nums[x] + nums[y] == target,
            forall|x: int, y: int| 0 <= x < i && 0 <= y < nums.len() && x != y ==> nums[x] + nums[y] != target,
        decreases nums.len() - i,
    {
        proof {
            lemma_solution_in_remaining(nums, target, i as int);
        }
        
        let mut j = 0;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                0 <= j <= nums.len(),
                exists|x: int, y: int| 0 <= x < nums.len() && 0 <= y < nums.len() && x != y && nums[x] + nums[y] == target,
                forall|x: int, y: int| 0 <= x < i && 0 <= y < nums.len() && x != y ==> nums[x] + nums[y] != target,
                forall|k: int| 0 <= k < j && (i as int) != k ==> nums[i as int] + nums[k] != target,
            decreases nums.len() - j,
        {
            if i != j && nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    
    proof {
        assert(forall|x: int, y: int| 0 <= x < nums.len() && 0 <= y < nums.len() && x != y ==> nums[x] + nums[y] != target);
        assert(exists|x: int, y: int| 0 <= x < nums.len() && 0 <= y < nums.len() && x != y && nums[x] + nums[y] == target);
        assert(false);
    }
    unreached()
}
// </vc-code>

fn main() {}
}