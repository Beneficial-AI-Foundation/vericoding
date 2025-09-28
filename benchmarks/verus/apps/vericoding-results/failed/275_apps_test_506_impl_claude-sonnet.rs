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
fn lemma_count_squares_base(a: int, b: int)
    requires a >= 0 && b >= 0, a == 0 || b == 0
    ensures count_squares(a, b) == 0
{
}

fn lemma_count_squares_equal(a: int)
    requires a > 0
    ensures count_squares(a, a) == 1
{
}

/* helper modified by LLM (iteration 5): fix integer literal syntax */
fn lemma_count_squares_nonneg(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures count_squares(a, b) >= 0
    decreases a + b
{
    if a == 0int || b == 0int {
    } else if a > b {
        lemma_count_squares_nonneg(a % b, b);
    } else if b > a {
        lemma_count_squares_nonneg(a, b % a);
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
    /* code modified by LLM (iteration 5): fix integer literal syntax */
    let mut x = a;
    let mut y = b;
    let mut result = 0i8;
    
    proof {
        lemma_count_squares_nonneg(x as int, y as int);
    }
    
    while x > 0 && y > 0
        invariant
            x >= 0,
            y >= 0,
            result >= 0,
            result as int + count_squares(x as int, y as int) == count_squares(a as int, b as int)
    {
        if x == y {
            proof {
                lemma_count_squares_equal(x as int);
            }
            result = result + 1;
            break;
        } else if x > y {
            let squares = (x / y) as i8;
            result = result + squares;
            x = x % y;
        } else {
            let squares = (y / x) as i8;
            result = result + squares;
            y = y % x;
        }
    }
    
    proof {
        lemma_count_squares_base(x as int, y as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}