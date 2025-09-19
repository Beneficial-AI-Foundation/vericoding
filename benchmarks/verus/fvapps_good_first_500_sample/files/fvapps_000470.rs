// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn num_ways(steps: u32, arr_len: u32) -> (result: u32)
    requires 
        steps >= 1,
        steps <= 500,
        arr_len >= 1,
        arr_len <= 1000000,
    ensures 
        1 <= result,
        result <= 1000000007,
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
    // assert_eq!(num_ways(3, 2), 4);
    // assert_eq!(num_ways(2, 4), 2);
    // assert_eq!(num_ways(4, 2), 8);
}