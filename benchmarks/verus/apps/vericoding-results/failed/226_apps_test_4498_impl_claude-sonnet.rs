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
/* helper modified by LLM (iteration 5): removed string properties lemma that caused compilation error */
spec fn abs_diff(x: int, y: int) -> int
{
    if x >= y { x - y } else { y - x }
}

proof fn lemma_abs_diff_properties(x: int, y: int)
    ensures
        abs_diff(x, y) >= 0,
        abs_diff(x, y) == abs_diff(y, x),
        abs_diff(x, y) == 0 <==> x == y,
{
}

proof fn lemma_can_communicate_correctness(a: int, b: int, c: int, d: int)
    ensures
        can_communicate(a, b, c, d) == (abs_diff(a, c) <= d || (abs_diff(a, b) <= d && abs_diff(b, c) <= d)),
{
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
    /* code modified by LLM (iteration 5): removed problematic string property proof and use string literals directly */
    let ghost a_int = a as int;
    let ghost b_int = b as int;
    let ghost c_int = c as int;
    let ghost d_int = d as int;
    
    proof {
        lemma_can_communicate_correctness(a_int, b_int, c_int, d_int);
    }
    
    let direct_dist = if a >= c { (a - c) as i8 } else { (c - a) as i8 };
    let via_b_dist_1 = if a >= b { (a - b) as i8 } else { (b - a) as i8 };
    let via_b_dist_2 = if b >= c { (b - c) as i8 } else { (c - b) as i8 };
    
    if direct_dist <= d || (via_b_dist_1 <= d && via_b_dist_2 <= d) {
        String::from("Yes")
    } else {
        String::from("No")
    }
}
// </vc-code>


}

fn main() {}