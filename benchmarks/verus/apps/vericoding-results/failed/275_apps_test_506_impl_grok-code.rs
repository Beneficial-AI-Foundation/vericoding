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
/* helper modified by LLM (iteration 5): changed parameters to int to avoid arithmetic overflow and match spec decreases */
fn count_squares_exec(a: int, b: int) -> (result: int)
    requires
        a >= 0,
        b >= 0
    ensures
        result == count_squares(a, b),
        (a > 0 && b > 0) ==> (result <= a),
        0 <= result <= 127
    decreases
        a + b when a >= 0 && b >= 0
{
    if a == 0 || b == 0 {
        0
    } else if a > b {
        if b == 0 { 0 } else {
            (a / b) + count_squares_exec(a % b, b)
        }
    } else if b > a {
        if a == 0 { 0 } else {
            (b / a) + count_squares_exec(a, b % a)
        }
    } else {
        1
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
/* code modified by LLM (iteration 5): adjusted parameter casts to int and return cast from int to i8 */
{
    let a_n = a as int;
    let b_n = b as int;
    let result_exec = count_squares_exec(a_n, b_n);
    result_exec as i8
}
// </vc-code>


}

fn main() {}