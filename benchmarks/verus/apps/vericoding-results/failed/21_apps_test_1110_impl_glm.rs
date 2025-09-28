// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int) -> bool {
        n >= 1
    }
    
    spec fn worst_case_presses(n: int) -> int
        recommends valid_input(n)
    {
        n * (n * n + 5) / 6
    }
// </vc-preamble>

// <vc-helpers>
fn worst_case_presses_impl(n: int) -> (result: int)
    requires valid_input(n)
    ensures result == worst_case_presses(n)
{
    if n == 1 {
        1
    } else {
        let smaller = worst_case_presses_impl(n - 1);
        smaller + n * (n + 1) / 2
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == worst_case_presses(n as int) && result as int >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix type conversion and result scope */
    let n_int = n as int;
    let result_int = worst_case_presses_impl(n_int);
    result_int as i8
}
// </vc-code>


}

fn main() {}