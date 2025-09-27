// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
const MAX_INT: i32 = 2147483647;
const MIN_INT: i32 = -2147483648;

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
fn divide(dividend: i32, divisor: i32) -> (result: i32)
    ensures
        MIN_INT <= result && result <= MAX_INT,
        divisor != 0 ==> (
            result != MAX_INT ==> int_abs((result as int) * (divisor as int) - (dividend as int)) < int_abs(divisor as int)
        ),
        divisor == 0 ==> result == MAX_INT,
        dividend == MIN_INT && divisor == -1 ==> result == MAX_INT,
        (dividend as int) * (divisor as int) > 0 ==> result >= 0,
        (dividend as int) * (divisor as int) < 0 && result != MAX_INT ==> result <= 0,
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
    // Apps difficulty: interview
    // Assurance level: unguarded

    // #eval divide 10 3
    // Expected: 3

    // #eval divide 7 -3  
    // Expected: -2

    // #eval divide -2147483648 -1
    // Expected: 2147483647
}