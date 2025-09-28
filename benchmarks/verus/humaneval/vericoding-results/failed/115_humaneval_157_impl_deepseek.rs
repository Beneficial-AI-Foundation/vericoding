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

/* helper modified by LLM (iteration 5): Remove ghost code from executable function */
fn safe_square(x: i8) -> i64 {
    (x as i64) * (x as i64)
}
// </vc-helpers>

// <vc-spec>
fn right_angle_triangle(a: i8, b: i8, c: i8) -> (result: bool)
    ensures result <==> valid_right_triangle(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i64 arithmetic to avoid overflow */
    if a <= 0 || b <= 0 || c <= 0 {
        return false;
    }
    
    let a64 = a as i64;
    let b64 = b as i64;
    let c64 = c as i64;
    
    if !(a64 + b64 > c64 && a64 + c64 > b64 && b64 + c64 > a64) {
        return false;
    }
    
    let sq_a = safe_square(a);
    let sq_b = safe_square(b);
    let sq_c = safe_square(c);
    
    sq_a + sq_b == sq_c ||
    sq_a + sq_c == sq_b ||
    sq_b + sq_c == sq_a
}
// </vc-code>


}

fn main() {}