// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_window_size(a: usize, b: usize, x: usize, y: usize) -> (result: usize)
    requires 
        a >= 1,
        b >= 1,
        x < a,
        y < b,
    ensures
        result == vstd::math::max(vstd::math::max(x * b, (a - 1 - x) * b), vstd::math::max(y * a, (b - 1 - y) * a)),
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
    // #eval max_window_size 8 8 0 0
    // #eval max_window_size 1 10 0 3  
    // #eval max_window_size 17 31 10 4
}