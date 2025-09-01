use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let n: usize = nums.len();
    let n_int: int = nums.len() as int;
    let mut i: usize = 0;
    while i < n
        invariant { i <= n }
        invariant {
            forall|a: int, b: int|
                0 <= a && a < b && b < n_int && a < i as int
                    ==> nums[a as usize] + nums[b as usize] != target
        }
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant { i < n }
            invariant { i + 1 <= j && j <= n }
            invariant {
                forall|b: int|
                    i as int + 1 <= b && b < j as int
                        ==> nums[i] + nums[b as usize] != target
            }
            invariant {
                forall|a: int, b: int|
                    0 <= a && a < b && b < n_int && a < i as int
                        ==> nums[a as usize] + nums[b as usize] != target
            }
            decreases n - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }

    proof {
        // From loop exit and invariant we get i == n
        assert(i == n);
        // From the outer invariant with i == n we get that no pair sums to target
        assert(forall|a: int, b: int|
            0 <= a && a < b && b < n_int
                ==> nums[a as usize] + nums[b as usize] != target);
        // This contradicts the precondition that such a pair exists
        assert(!(exists|a: int, b: int|
            0 <= a && a < b && b < n_int && nums[a as usize] + nums[b as usize] == target));
        // Contradiction
        assert(false);
    }

    // unreachable, but needed for Rust syntactic return
    (0usize, 0usize)
}
// </vc-code>

fn main() {}
}