use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this verification.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
    // pre-conditions-start
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: nat = nums.len();

    let mut i: nat = 0;
    while i < n {
        invariant(i <= n);
        invariant(forall |p: nat, q: nat| #[trigger] (p < q && q < i) ==> ((nums[p as usize] as int) + (nums[q as usize] as int) != (target as int)));

        let mut j: nat = i + 1;
        while j < n {
            invariant(i < n);
            invariant(j <= n);
            invariant(forall |p: nat, q: nat| #[trigger] (p < q && q < i) ==> ((nums[p as usize] as int) + (nums[q as usize] as int) != (target as int)));
            invariant(forall |q2: nat| #[trigger] (i < q2 && q2 < j) ==> ((nums[i as usize] as int) + (nums[q2 as usize] as int) != (target as int)));

            if (nums[i as usize] as int) + (nums[j as usize] as int) == (target as int) {
                proof {
                    let pi: int = i as int;
                    let qi: int = j as int;
                    // bounds
                    assert(0 <= pi);
                    assert(0 <= qi);
                    assert(pi < qi);
                    assert(qi < n as int);
                    // equality
                    assert((nums[pi as usize] as int) + (nums[qi as usize] as int) == (target as int));
                    // existential witness
                    assert(exists |p0: int, q0: int| 0 <= p0 < q0 < n as int && (nums[p0 as usize] as int) + (nums[q0 as usize] as int) == (target as int));
                }
                return true;
            }

            j += 1;
        }

        i += 1;
    }

    proof {
        // loop finished, so i >= n and invariant i <= n gives i == n
        assert(i >= n);
        assert(i <= n);
        assert(i == n);

        // from the invariant we have no pair with second index < i (which equals n)
        assert(forall |p: nat, q: nat| #[trigger] (p < q && q < i) ==> ((nums[p as usize] as int) + (nums[q as usize] as int) != (target as int)));

        // show no int indices satisfy the existence
        assert(!exists |pi: int, qi: int| 0 <= pi < qi < n as int && (nums[pi as usize] as int) + (nums[qi as usize] as int) == (target as int));
    }

    false
    // impl-end
}
// </vc-code>

fn main() {}
}