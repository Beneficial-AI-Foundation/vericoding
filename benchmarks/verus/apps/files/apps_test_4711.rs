// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000
}

spec fn min_of_three(x: int, y: int, z: int) -> int {
    if x <= y && x <= z { x }
    else if y <= z { y }
    else { z }
}

spec fn correct_result(a: int, b: int, c: int) -> int {
    min_of_three(a + b, a + c, b + c)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int)
    ensures result as int == correct_result(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}