// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calc_min_days(n: u64, g: u64, b: u64) -> (result: u64)
    requires 
        n > 0,
        g > 0,
        b > 0,
    ensures 
        result >= n,
        result >= (n + 1) / 2,
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
    // #eval calc_min_days 5 1 1
    // #eval calc_min_days 8 10 10  
    // #eval calc_min_days 1000000 1 1000000
}