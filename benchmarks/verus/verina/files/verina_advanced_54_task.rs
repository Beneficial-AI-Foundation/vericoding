// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn missing_number_precond(nums: &Vec<usize>) -> bool {
    (forall|i: int| 0 <= i < nums.len() ==> nums[i] <= nums.len()) &&
    nums.no_duplicates()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn missing_number(nums: &Vec<usize>) -> (result: usize)
    requires missing_number_precond(nums),
    ensures
        result <= nums.len(),
        !nums.contains(&result),
        forall|x: usize| x <= nums.len() && x != result ==> nums.contains(&x),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}