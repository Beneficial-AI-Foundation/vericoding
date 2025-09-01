use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = nums.len();
    proof {
        assert(n >= 2);
    }

    let mut i: usize = 0;
    while i < n
        invariant i <= n,
        invariant (i as int) >= 0,
    {
        let mut j: usize = (i as nat) + 1;
        while j < n
            invariant 
                i < n, /* from outer loop inv and current loop progress */
                j <= n, /* loop termination condition */
                (i as int) >= 0, /* from outer loop inv */
                (j as int) >= 0, /* from initialization and loop progress */
                (i as int) < (j as int), /* from initialization (j = i+1) and loop progress */
        {
            let num_i = nums[i as int];
            let num_j = nums[j as int];

            if num_i + num_j == target {
                proof {
                    // i < j implies i != j already known to verus
                    assert(i != j); 
                    // Verify array access bounds
                    assert(0 <= i && i < n);
                    assert(0 <= j && j < n);
                    // Verify return condition
                    assert(nums[i as int] + nums[j as int] == target);
                }
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    // This part should be unreachable given the precondition that a solution always exists.
    // However, Rust requires a return value for all paths.
    // The verifier should be able to prove this unreachable.
    unreachable!();
}
// </vc-code>

fn main() {}
}