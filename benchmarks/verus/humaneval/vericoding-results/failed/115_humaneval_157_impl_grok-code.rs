// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adjusted spec functions to int types for overflow-free spec verification */
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
    /* code modified by LLM (iteration 5): Cast to i64 for arithmetic to prevent possible overflow in multiplication and addition */
    let a_i = a as i64;
    let b_i = b as i64;
    let c_i = c as i64;
    let result = a_i > 0 && b_i > 0 && c_i > 0 &&
        a_i + b_i > c_i && a_i + c_i > b_i && b_i + c_i > a_i &&
        (a_i * a_i + b_i * b_i == c_i * c_i ||
         a_i * a_i + c_i * c_i == b_i * b_i ||
         b_i * b_i + c_i * c_i == a_i * a_i);
    result
}
// </vc-code>


}

fn main() {}