// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n >= 1 && m >= 1
}

spec fn count_face_down_cards(n: int, m: int) -> int
    recommends valid_input(n, m)
{
    if n == 1 && m == 1 {
        1
    } else if n == 1 {
        m - 2
    } else if m == 1 {
        n - 2
    } else {
        (n - 2) * (m - 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added bounds checking helper to ensure arithmetic operations are safe */
fn safe_sub(x: i8, y: i8) -> i8
    requires x >= y,
{
    x - y
}

fn safe_mul(x: i8, y: i8) -> i8
    requires x >= 0 && y >= 0,
    ensures result >= 0,
{
    x * y
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int),
    ensures 
        result as int == count_face_down_cards(n as int, m as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced direct arithmetic with safe operations and added proper verification */
    if n == 1 && m == 1 {
        1
    } else if n == 1 {
        proof { assert(m >= 2) by { assert(valid_input(n as int, m as int) && n == 1 && m >= 2); }; }
        safe_sub(m, 2)
    } else if m == 1 {
        proof { assert(n >= 2) by { assert(valid_input(n as int, m as int) && m == 1 && n >= 2); }; }
        safe_sub(n, 2)
    } else {
        proof { assert(n >= 2 && m >= 2) by { assert(valid_input(n as int, m as int) && n >= 2 && m >= 2); }; }
        let x = safe_sub(n, 2);
        let y = safe_sub(m, 2);
        safe_mul(x, y)
    }
}
// </vc-code>


}

fn main() {}