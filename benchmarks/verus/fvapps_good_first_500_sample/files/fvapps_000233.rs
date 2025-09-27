// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seq_sum(nums: Seq<u32>) -> int
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else {
        nums[0] as int + seq_sum(nums.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn num_subarrays_with_sum(nums: Vec<u32>, target: u32) -> (result: u32)
    requires forall|i: int| 0 <= i < nums.len() ==> nums[i] <= 1,
    ensures 
        target as int > seq_sum(nums@) ==> result == 0,
        nums@.len() > 0 && seq_sum(nums@) > 0 && target as int == seq_sum(nums@) ==> result >= 1,
        target == 0 && nums@.len() > 0 && (forall|i: int| 0 <= i < nums.len() ==> nums[i] == 0) 
            ==> result == (nums@.len() as u32 * (nums@.len() as u32 + 1)) / 2,
        nums@.len() > 0 && seq_sum(nums@) > 0 && target == 1 ==> result as int >= seq_sum(nums@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {
    // let result1 = num_subarrays_with_sum(vec![1, 0, 1, 0, 1], 2);
    // assert(result1 == 4);
    
    // let result2 = num_subarrays_with_sum(vec![0, 0, 0, 0, 0], 0);
    // assert(result2 == 15);
}