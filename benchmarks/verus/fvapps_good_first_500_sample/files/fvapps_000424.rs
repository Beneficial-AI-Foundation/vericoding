// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_subarray_ones_after_delete(nums: Vec<u32>) -> (result: u32)
    requires 
        nums.len() > 0,
        forall|i: int| 0 <= i < nums.len() ==> nums[i] <= 1,
    ensures 
        result >= 0,
        result <= nums.len()
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

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded

    // let test1 = vec![1, 1, 0, 1];
    // assert_eq!(longest_subarray_ones_after_delete(test1), 3);

    // let test2 = vec![0, 1, 1, 1, 0, 1, 1, 0, 1];
    // assert_eq!(longest_subarray_ones_after_delete(test2), 5);

    // let test3 = vec![1, 1, 1];
    // assert_eq!(longest_subarray_ones_after_delete(test3), 2);
}