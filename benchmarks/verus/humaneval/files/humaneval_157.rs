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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}