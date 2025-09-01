use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let n_int: int = n as int;

    let mut i: nat = 0;
    while i < n {
        let i_int: int = i as int;
        invariant 0 <= i && i <= n;
        invariant forall |p: int, q: int| #[trigger] 0 <= p && p < q && q < n_int && p < i_int ==>
            (nums[p as usize] as int) + (nums[q as usize] as int) != (target as int);
        let mut j: nat = i + 1;
        while j < n {
            let j_int: int = j as int;
            invariant 0 <= i && i < n;
            invariant 0 <= j && j <= n;
            invariant forall |p: int, q: int| #[trigger] 0 <= p && p < q && q < n_int && p < i_int ==>
                (nums[p as usize] as int) + (nums[q as usize] as int) != (target as int);
            invariant forall |q2: int| #[trigger] 0 <= q2 && i_int < q2 && q2 < j_int ==>
                (nums[i as usize] as int) + (nums[q2 as usize] as int) != (target as int);

            if (nums[i as usize] as int) + (nums[j as usize] as int) == (target as int) {
                return true;
            }

            j += 1;
        }

        i += 1;
    }

    false
    // impl-end
}
// </vc-code>

fn main() {}
}