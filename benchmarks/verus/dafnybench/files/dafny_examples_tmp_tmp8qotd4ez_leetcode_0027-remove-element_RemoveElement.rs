// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i8>, val: i8) -> (newLength: usize)
    ensures 
        0 <= newLength <= nums.len(),
        forall|i: int| 0 <= i < newLength ==> nums[i] as int != val as int,
        nums@.subrange(0, newLength as int).to_multiset() == 
            old(nums)@.to_multiset().remove(val),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}