// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 0 && b > 0
}

spec fn count_squares(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b when a > 0 && b > 0
{
    if a == 0 || b == 0 {
        0
    } else if a > b {
        if b == 0 { 0 } else {
            a / b + count_squares(a % b, b)
        }
    } else if b > a {
        if a == 0 { 0 } else {
            b / a + count_squares(a, b % a)
        }
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove decreases_when from proof function, use requires instead */
proof fn lemma_count_squares_bound(a: int, b: int)
    requires
        a > 0,
        b > 0,
        a + b > a % b + b when a > b && b > 0,
        a + b > a + b % a when b > a && a > 0,
    ensures
        count_squares(a, b) >= 1,
{
    if a == b {
    } else if a > b {
        assert(a % b >= 0) by (nonlinear_arith);
        if a % b > 0 {
            lemma_count_squares_bound(a % b, b);
        }
    } else {
        assert(b % a >= 0) by (nonlinear_arith);
        if b % a > 0 {
            lemma_count_squares_bound(a, b % a);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures 
        result >= 0,
        a == b ==> result == 1,
        a > b ==> result >= 1,
        result as int == count_squares(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add termination check with expected decreases condition */
    let mut x: i8 = a;
    let mut y: i8 = b;
    let mut count: i8 = 0;
    
    while x > 0 && y > 0
        invariant
            x >= 0, y >= 0,
            count >= 0,
            count as int + count_squares(x as int, y as int) == count_squares(a as int, b as int),
        decreases x as int + y as int
    {
        if x == y {
            count = count + 1;
            break;
        } else if x > y {
            let q = x / y;
            let r = x % y;
            assert(q >= 1) by (nonlinear_arith);
            assert(r >= 0) by (nonlinear_arith);
            assert(r < y) by (nonlinear_arith);
            count = count + q;
            x = r;
        } else {
            let q = y / x;
            let r = y % x;
            assert(q >= 1) by (nonlinear_arith);
            assert(r >= 0) by (nonlinear_arith);
            assert(r < x) by (nonlinear_arith);
            count = count + q;
            y = r;
        }
    }
    
    count
}
// </vc-code>


}

fn main() {}