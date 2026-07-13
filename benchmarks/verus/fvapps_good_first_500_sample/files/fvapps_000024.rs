// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn int_to_float(x: i32) -> f64 {
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn solve_equation(d: i32) -> (result: (bool, f64, f64))
    ensures
        d >= 5 && d <= 1000 ==> result.0 == true,
        d <= 0 && d >= -1000 ==> result.0 == true,
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
fn main() {}