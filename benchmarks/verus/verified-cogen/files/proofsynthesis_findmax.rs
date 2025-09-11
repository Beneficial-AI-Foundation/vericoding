// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_max(nums: Vec<i32>) -> (ret:i32)

    requires
        nums.len() > 0,

    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}