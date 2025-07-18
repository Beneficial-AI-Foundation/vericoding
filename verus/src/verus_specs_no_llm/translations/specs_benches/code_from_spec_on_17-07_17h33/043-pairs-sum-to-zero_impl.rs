use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    /* code modified by LLM (iteration 2): moved requires/ensures clauses to correct position immediately after function signature */
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
    /* code modified by LLM (iteration 2): implemented proper nested loop algorithm to find pairs that sum to target */
    let mut i = 0;
    while i < nums.len() - 1
        invariant
            0 <= i <= nums.len() - 1,
            forall|x: int, y: int| 0 <= x < i && x < y < nums.len() ==> nums[x] + nums[y] != target,
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len() - 1,
                i + 1 <= j <= nums.len(),
                forall|x: int, y: int| 0 <= x < i && x < y < nums.len() ==> nums[x] + nums[y] != target,
                forall|y: int| i < y < j ==> nums[i] + nums[y] != target,
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