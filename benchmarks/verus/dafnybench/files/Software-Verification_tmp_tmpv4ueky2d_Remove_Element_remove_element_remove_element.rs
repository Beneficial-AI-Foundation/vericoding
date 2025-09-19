// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i8>, val: i8) -> (i: usize)
    requires 
        old(nums)@.len() <= 100,
        forall|j: int| 0 <= j < old(nums)@.len() ==> #[trigger] old(nums)@[j] as int >= 0 && old(nums)@[j] as int <= 50,
        0 <= val as int <= 100,
    ensures
        forall|j: int| 0 < j < i as int && j < nums@.len() ==> #[trigger] nums@[j] as int != val as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}