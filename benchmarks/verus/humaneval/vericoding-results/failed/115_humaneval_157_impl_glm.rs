// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_triangle(a: int, b: int, c: int) -> bool {
    a > 0 && b > 0 && c > 0 &&
    a + b > c && a + c > b && b + c > a
}

spec fn is_right_triangle(a: int, b: int, c: int) -> bool {
    a * a + b * b == c * c || 
    a * a + c * c == b * b || 
    b * b + c * c == a * a
}

spec fn valid_right_triangle(a: int, b: int, c: int) -> bool {
    valid_triangle(a, b, c) && is_right_triangle(a, b, c)
}
// </vc-helpers>

// <vc-spec>
fn right_angle_triangle(a: i8, b: i8, c: i8) -> (result: bool)
    ensures result <==> valid_right_triangle(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): adding bounds assertions to prevent overflow */
    let a_large = a as i64;
    let b_large = b as i64;
    let c_large = c as i64;
    let valid = a_large > 0 && b_large > 0 && c_large > 0 &&
                a_large + b_large > c_large &&
                a_large + c_large > b_large &&
                b_large + c_large > a_large;

    // Assert the bounds of the converted values to prevent overflow in multiplication
    assert(a_large >= i8::MIN as i64 && a_large <= i8::MAX as i64);
    assert(b_large >= i8::MIN as i64 && b_large <= i8::MAX as i64);
    assert(c_large >= i8::MIN as i64 && c_large <= i8::MAX as i64);

    // Now compute the squares safely
    let a_sq = a_large * a_large;
    let b_sq = b_large * b_large;
    let c_sq = c_large * c_large;

    let right = (a_sq + b_sq == c_sq) ||
                (a_sq + c_sq == b_sq) ||
                (b_sq + c_sq == a_sq);

    valid && right
}
// </vc-code>


}

fn main() {}