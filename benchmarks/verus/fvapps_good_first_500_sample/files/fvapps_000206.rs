// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i >= 0 { i } else { -i }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn contains_nearby_almost_duplicate(nums: Vec<i32>, k: i32, t: i32) -> (result: bool)
    ensures 
        (k <= 0 && t < 0) ==> !result,
        (k > 0 && t >= 0 && nums.len() >= 2 && nums.len() <= 100) ==> (
            result == exists|i: int, j: int| 
                0 <= i && i < nums.len() &&
                0 <= j && j < nums.len() &&
                i != j &&
                abs_spec(i - j) <= k &&
                abs_spec(nums[i] - nums[j]) <= t
        )
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
    // #eval contains_nearby_almost_duplicate(vec![1, 2, 3, 1], 3, 0);
    // #eval contains_nearby_almost_duplicate(vec![1, 0, 1, 1], 1, 2);
    // #eval contains_nearby_almost_duplicate(vec![1, 5, 9, 1, 5, 9], 2, 3);
}