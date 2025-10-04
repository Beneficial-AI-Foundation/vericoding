// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn subarrays_div_by_k(nums: Vec<i32>, k: i32) -> (result: i32)
    requires 
        nums.len() >= 1,
        nums.len() <= 30000,
        k >= 2,
        k <= 10000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= -10000 && #[trigger] nums[i] <= 10000,
    ensures
        result >= 0,
        k == 5 && nums@ == seq![4i32, 5i32, 0i32, -2i32, -3i32, 1i32] ==> result == 7,
        k == 5 && nums@ == seq![5i32] ==> result == 1,
        k == 5 && nums@ == seq![4i32, 5i32, 0i32, -2i32, -3i32, 1i32, 5i32] ==> result == 9
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview
   Assurance level: guarded_and_plausible */

}

fn main() {
    // #eval subarraysDivByK [4, 5, 0, -2, -3, 1] 5
    // Expected: 7
    
    // #eval subarraysDivByK [5] 5
    // Expected: 1
    
    // #eval subarraysDivByK [4, 5, 0, -2, -3, 1, 5] 5
    // Expected: 9
}