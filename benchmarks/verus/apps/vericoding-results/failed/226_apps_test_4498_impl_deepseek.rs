// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn can_communicate(a: int, b: int, c: int, d: int) -> bool {
    (if a - c >= 0 { a - c } else { c - a }) <= d || 
    (((if a - b >= 0 { a - b } else { b - a }) <= d) && 
     ((if b - c >= 0 { b - c } else { c - b }) <= d))
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): fix compilation errors by using proper exec types */
proof fn can_communicate_equivalent(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d),
    ensures
        can_communicate(a, b, c, d) <==> (abs_diff(a, c) <= d || (abs_diff(a, b) <= d && abs_diff(b, c) <= d)),
{
}

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int, d as int),
    ensures 
        result@ == seq!['Y', 'e', 's'] <==> can_communicate(a as int, b as int, c as int, d as int),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix compilation errors by avoiding nat/int conversions */
    let ab = if a >= b { a - b } else { b - a };
    let bc = if b >= c { b - c } else { c - b };
    let ac = if a >= c { a - c } else { c - a };
    
    let result: String;
    if ac <= d || (ab <= d && bc <= d) {
        result = "Yes".to_string();
    } else {
        result = "No".to_string();
    }
    result
}
// </vc-code>


}

fn main() {}