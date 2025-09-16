// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)

    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,

    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed type errors by using usize for loop variables and converting to int in ghost contexts */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i as int <= nums.len() as int,
            forall|i_prime: int, j_prime: int|
                0 <= i_prime < i as int && i_prime < j_prime < nums.len() as int ==> nums[i_prime] + nums[j_prime] != target,
        decreases (nums.len() as int) - (i as int)
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i as int + 1 <= j as int <= nums.len() as int,
                forall|j_prime: int|
                    i as int + 1 <= j_prime < j as int ==> nums[i as int] + nums[j_prime] != target,
            decreases (nums.len() as int) - (j as int)
        {
            if nums[i] + nums[j] == target {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}