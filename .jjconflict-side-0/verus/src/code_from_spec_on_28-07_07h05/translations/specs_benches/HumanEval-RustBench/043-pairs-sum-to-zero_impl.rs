use vstd::prelude::*;

verus! {

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
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|ii: int, jj: int| 0 <= ii < i && ii < jj < nums.len() ==> nums[ii] + nums[jj] != target,
        /* code modified by LLM (iteration 1): added decreases clause to prove termination */
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall|ii: int, jj: int| 0 <= ii < i && ii < jj < nums.len() ==> nums[ii] + nums[jj] != target,
                /* code modified by LLM (iteration 1): fixed type mismatch by casting i to int in invariant */
                forall|jj: int| (i as int) < jj < j ==> nums[i as int] + nums[jj] != target,
            /* code modified by LLM (iteration 1): added decreases clause to prove termination */
            decreases nums.len() - j
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

}
fn main() {}