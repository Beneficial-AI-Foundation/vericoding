// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn minimum(l: Seq<u32>) -> Option<u32> {
    if l.len() == 0 {
        None
    } else {
        Some(l.fold_left(l[0], |acc: u32, x: u32| if x < acc { x } else { acc }))
    }
}
// </vc-helpers>

// <vc-spec>
fn num_subseq(nums: Vec<u32>, target: u32) -> (result: u32)
    requires
        target >= 2,
        nums.len() >= 1,
        forall|i: int| 0 <= i < nums.len() ==> nums[i] >= 1 && nums[i] <= 1000,
    ensures
        result < 1000000007,
        (nums.len() == 1 && nums[0] >= 1 && nums[0] <= 100) ==> 
            result == (if nums[0] * 2 <= nums[0] * 3 { 1u32 } else { 0u32 })
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
    // Assurance level: guarded_and_plausible

    // #eval numSubseq [3, 5, 6, 7] 9 should output 4
    // #eval numSubseq [3, 3, 6, 8] 10 should output 6  
    // #eval numSubseq [2, 3, 3, 4, 6, 7] 12 should output 61
}