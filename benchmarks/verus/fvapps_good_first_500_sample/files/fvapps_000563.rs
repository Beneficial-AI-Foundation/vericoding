// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calc_max_second_screen(n: u64, b: u64) -> (result: u64)
    requires
        n >= 1,
        b >= 1,
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // assert(calc_max_second_screen(10, 2) == 12);
    // assert(calc_max_second_screen(8, 5) == 3);
    // assert(calc_max_second_screen(6, 1) == 9);
}