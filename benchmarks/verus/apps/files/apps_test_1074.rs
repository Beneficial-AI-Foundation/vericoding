// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_ones_in_octal(a: int) -> int
    decreases a when a >= 0
{
    if a == 0 {
        0int
    } else {
        (if a % 8 == 1 { 1int } else { 0int }) + count_ones_in_octal(a / 8)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int) -> (count: int)
    requires 
        a >= 0,
    ensures 
        count >= 0,
        count == count_ones_in_octal(a),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}