// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn max_spec(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

spec fn time_without_coverage_spec(a: int, b: int, c: int, r: int) -> int;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn time_without_coverage(a: i32, b: i32, c: i32, r: i32) -> (result: i32)
    ensures 
        result >= 0,
        time_without_coverage_spec(a as int, b as int, c as int, r as int) == 
        time_without_coverage_spec(b as int, a as int, c as int, r as int)
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

    // Example test cases:
    // time_without_coverage(1, 10, 7, 1) should return 7
    // time_without_coverage(3, 3, 3, 0) should return 0
    // time_without_coverage(8, 2, 10, 4) should return 4
}