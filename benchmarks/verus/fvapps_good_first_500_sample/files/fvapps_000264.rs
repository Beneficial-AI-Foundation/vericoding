// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn can_jump(nums: Vec<nat>) -> (result: bool)
    requires nums.len() > 0,
    ensures
        /* Single element arrays are always reachable */
        nums.len() == 1 ==> result == true,
        /* If all non-last elements are non-zero, end is reachable */
        (nums.len() > 0 && forall|i: int| 0 <= i < nums.len() - 1 ==> nums[i] > 0) ==> result == true,
        /* If first element is zero and array has more than one element, end is not reachable */
        (nums.len() > 1 && nums[0] == 0) ==> result == false,
        /* If there's a zero at position and we can still reach the end, 
           then there must be some earlier position that can jump past it */
        forall|idx: int| 0 <= idx < nums.len() - 1 && nums[idx] == 0 && result == true ==>
            exists|j: int| 0 <= j < idx && j + nums[j] > idx
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>

}

fn main() {
    // /* Apps difficulty: interview */
    // /* Assurance level: unguarded */

    // /* Example evaluations */
    // /* can_jump([2, 3, 1, 1, 4]) should return true */
    // /* can_jump([3, 2, 1, 0, 4]) should return false */
    // /* can_jump([0]) should return true */
}