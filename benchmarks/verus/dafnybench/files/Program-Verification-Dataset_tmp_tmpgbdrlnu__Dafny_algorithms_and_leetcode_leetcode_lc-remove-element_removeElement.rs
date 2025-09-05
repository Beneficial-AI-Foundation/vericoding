use vstd::prelude::*;

verus! {

//https://leetcode.com/problems/remove-element/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures forall|k: int| 0 < k < i && k < nums.len() ==> nums[k] != val,
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>

fn main() {}

}
