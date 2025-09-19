// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn find_max(x: int, y: int) -> int {
    if x > y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i8>) -> (max: i8)
    requires 
        1 <= nums@.len() <= 2500,
        forall|i: int| 0 <= i < nums@.len() ==> #[trigger] nums@[i] as int >= -10000 && #[trigger] nums@[i] as int <= 10000,

    ensures 
        max as int >= 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}