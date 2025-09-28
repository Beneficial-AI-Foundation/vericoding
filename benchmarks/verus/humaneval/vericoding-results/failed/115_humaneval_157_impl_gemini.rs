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
/* code modified by LLM (iteration 5): [use i64 for calculations to prevent overflow errors] */
{
    if a <= 0 || b <= 0 || c <= 0 {
        return false;
    }

    let a_64 = a as i64;
    let b_64 = b as i64;
    let c_64 = c as i64;

    if a_64 + b_64 <= c_64 || a_64 + c_64 <= b_64 || b_64 + c_64 <= a_64 {
        return false;
    }

    let a_sq = a_64 * a_64;
    let b_sq = b_64 * b_64;
    let c_sq = c_64 * c_64;

    a_sq + b_sq == c_sq || a_sq + c_sq == b_sq || b_sq + c_sq == a_sq
}

// </vc-code>


}

fn main() {}