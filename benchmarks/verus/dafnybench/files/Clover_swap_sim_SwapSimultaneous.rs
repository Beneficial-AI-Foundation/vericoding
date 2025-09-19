// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap_simultaneous(x_param: i8, y_param: i8) -> (ret: (i8, i8))
    ensures 
        ret.0 == y_param,
        ret.1 == x_param,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}