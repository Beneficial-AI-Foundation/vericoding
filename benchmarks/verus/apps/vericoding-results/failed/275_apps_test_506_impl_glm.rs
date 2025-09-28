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
fn count_squares_recursive(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures result >= 0
    ensures result as int == count_squares(a as int, b as int)
    decreases (a as int) + (b as int)
{
    if a == b {
        1
    } else if a > b {
        let q = a / b;
        let r = a % b;
        if r == 0 {
            q
        } else {
            q + count_squares_recursive(r, b)
        }
    } else {
        let q = b / a;
        let r = b % a;
        if r == 0 {
            q
        } else {
            q + count_squares_recursive(a, r)
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
    count_squares_recursive(a, b)
}
// </vc-code>


}

fn main() {}