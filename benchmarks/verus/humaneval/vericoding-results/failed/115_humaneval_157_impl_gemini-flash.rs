// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change. Helpers were correct. */
spec fn valid_triangle(a: int, b: int, c: int) -> bool {
    a > 0 && b > 0 && c > 0 &&
    a + b > c && a + c > b && b + c > a
}

spec fn valid_right_triangle(a: int, b: int, c: int) -> bool {
    valid_triangle(a, b, c) && (
    a * a + b * b == c * c || 
    a * a + c * c == b * b || 
    b * b + c * c == a * a
    )
}
// </vc-helpers>

// <vc-spec>
fn right_angle_triangle(a: i8, b: i8, c: i8) -> (result: bool)
    ensures result <==> valid_right_triangle(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous `int` casts within the `exec` context of the main function caused compilation errors because `int` should only be used in ghost contexts. The fix is to remove the explicit `as int` casts; Verus will implicitly cast `i8` to `int` when passed to a `spec` function which expects `int` arguments. */
{
    valid_right_triangle(a, b, c)
}
// </vc-code>


}

fn main() {}