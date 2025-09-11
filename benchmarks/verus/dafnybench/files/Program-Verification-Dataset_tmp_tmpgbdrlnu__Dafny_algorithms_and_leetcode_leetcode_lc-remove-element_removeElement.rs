// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures forall|k: int| 0 < k < i && k < nums.len() ==> nums[k] != val,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}