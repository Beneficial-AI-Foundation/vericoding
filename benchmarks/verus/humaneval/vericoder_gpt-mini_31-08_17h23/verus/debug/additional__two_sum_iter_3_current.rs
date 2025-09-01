use vstd::prelude::*;

verus! {

// <vc-helpers>
/* No helpers required */
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
    let n = nums.len();

    let mut i: usize = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant forall|u: int, v: int| { 0 <= u && u < (i as int) && u < v && v < (n as int)
                ==> nums[u] + nums[v] != target }
        decreases (n as int - i as int)
    {
        let mut j: usize = i + 1;
        while j < n
            invariant i + 1 <= j && j <= n
            invariant forall|k: int| { (i as int) + 1 <= k && k < (j as int) ==> nums[i as int] + nums[k] != target }
            decreases (n as int - j as int)
        {
            if nums[i as int] + nums[j as int] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    // By the precondition there exists a pair summing to target, so the above loop is unreachable.
    proof {
        let (p, q) = choose(|p: int, q: int|
            0 <= p && p < q && q < (n as int) && nums[p] + nums[q] == target
        );
        // Loop termination implies i == n
        assert(i == n);
        // From the outer invariant we have no pair for u < i
        assert(forall|u: int, v: int| 0 <= u && u < (i as int) && u < v && v < (n as int)
            ==> nums[u] + nums[v] != target);
        // Instantiate the invariant with p and q to get contradiction
        assert(0 <= p);
        assert(p < (i as int));
        assert(p < q);
        assert(q < (n as int));
        assert(nums[p] + nums[q] == target);
        // Contradiction
        assert(false);
    }

    // Unreachable, but return something to satisfy Rust syntax
    (0, 1)
    // impl-end
}
// </vc-code>

fn main() {}
}