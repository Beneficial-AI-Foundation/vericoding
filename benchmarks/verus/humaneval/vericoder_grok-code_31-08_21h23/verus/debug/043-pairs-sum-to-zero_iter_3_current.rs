use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
HELPERS : auxiliary code and proofs
// </vc-helpers>
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
    let s: Seq<i32> = nums.view();
    let mut found: bool = false;
    #[verifier::loop_isolation(false)]
    for i in 0..(s.len() as int) {
        #[verifier::loop_isolation(false)]
        for j in (i + 1)..(s.len() as int) {
            if s[i] + s[j] == target {
                found = true;
            }
        }
    }
    found
}
// </vc-code>

fn main() {}
}