// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn swap_simultaneous(x_param: i32, y_param: i32) -> (ret: (i32, i32))
    ensures 
        ret.0 == y_param,
        ret.1 == x_param,
// </vc-spec>
// <vc-code>
{
    (y_param, x_param)
}
// </vc-code>

}
fn main() {}