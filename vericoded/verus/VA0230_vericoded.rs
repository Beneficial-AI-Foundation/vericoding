// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 99
}

spec fn expected_result(n: int) -> bool
    recommends valid_input(n)
{
    if n < 12 {
        if n == 1 || n == 7 || n == 9 || n == 10 || n == 11 {
            false
        } else {
            true
        }
    } else if 12 < n < 30 {
        false
    } else if 69 < n < 80 {
        false
    } else if 89 < n {
        false
    } else {
        let last_digit = n % 10;
        if last_digit != 1 && last_digit != 7 && last_digit != 9 {
            true
        } else {
            false
        }
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: bool)
requires 
    valid_input(n as int),
ensures 
    result == expected_result(n as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed ghost int conversion, work directly with i8 */
    if n < 12 {
        if n == 1 || n == 7 || n == 9 || n == 10 || n == 11 {
            false
        } else {
            true
        }
    } else if 12 < n && n < 30 {
        false
    } else if 69 < n && n < 80 {
        false
    } else if 89 < n {
        false
    } else {
        let last_digit = n % 10;
        if last_digit != 1 && last_digit != 7 && last_digit != 9 {
            true
        } else {
            false
        }
    }
}
// </vc-code>


}

fn main() {}