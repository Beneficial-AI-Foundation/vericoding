// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(nums: Seq<u32>, value: u32) -> nat
    decreases nums.len()
{
    if nums.len() == 0 {
        0nat
    } else {
        (if nums[0] == value { 1nat } else { 0nat }) + count_occurrences(nums.skip(1), value)
    }
}

fn rearrange_caps(nums: Vec<u32>) -> (result: Option<Vec<u32>>)
    ensures 
        match result {
            Some(caps) => {
                &&& caps.len() == nums.len()
                &&& (forall|i: int| 0 <= i < caps.len() ==> caps[i] != nums[i])
                &&& (forall|value: u32| count_occurrences(nums@, value) == count_occurrences(caps@, value))
            },
            None => {
                exists|majority_value: u32| count_occurrences(nums@, majority_value) > nums.len() / 2
            }
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    None
    // impl-end
}
// </vc-code>


}
fn main() {}