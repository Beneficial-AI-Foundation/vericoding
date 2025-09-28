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
    /* code modified by LLM (iteration 5): using ghost variables for int arithmetic */
    let ghost a_int = a as int;
    let ghost b_int = b as int;
    let ghost c_int = c as int;
    
    if a <= 0 || b <= 0 || c <= 0 {
        return false;
    }
    
    if a as u8 + b as u8 <= c as u8 || a as u8 + c as u8 <= b as u8 || b as u8 + c as u8 <= a as u8 {
        return false;
    }
    
    let a_squared = (a as i64) * (a as i64);
    let b_squared = (b as i64) * (b as i64);
    let c_squared = (c as i64) * (c as i64);
    
    let result = a_squared + b_squared == c_squared || 
                 a_squared + c_squared == b_squared || 
                 b_squared + c_squared == a_squared;
    
    result
}
// </vc-code>


}

fn main() {}