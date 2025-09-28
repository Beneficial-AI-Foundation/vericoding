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
    /* code modified by LLM (iteration 5): use i32 arithmetic throughout to avoid int type in exec code */
    if a <= 0 || b <= 0 || c <= 0 {
        return false;
    }
    
    // Check triangle inequality using i32
    let a_i32 = a as i32;
    let b_i32 = b as i32;
    let c_i32 = c as i32;
    
    if a_i32 + b_i32 <= c_i32 || a_i32 + c_i32 <= b_i32 || b_i32 + c_i32 <= a_i32 {
        return false;
    }
    
    // Use i32 for computation to avoid overflow
    let a_sq = a_i32 * a_i32;
    let b_sq = b_i32 * b_i32;
    let c_sq = c_i32 * c_i32;
    
    (a_sq + b_sq == c_sq) || (a_sq + c_sq == b_sq) || (b_sq + c_sq == a_sq)
}
// </vc-code>


}

fn main() {}