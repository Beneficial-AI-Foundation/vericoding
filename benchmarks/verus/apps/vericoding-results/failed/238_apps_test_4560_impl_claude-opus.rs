// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int) -> bool {
    1 <= n <= 10000 && 0 <= a <= 1000
}

spec fn can_pay_exactly(n: int, a: int) -> bool {
    n % 500 <= a
}

spec fn valid_output(result: String) -> bool {
    result@ == "Yes"@ || result@ == "No"@
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8) -> (result: String)
    requires 
        valid_input(n as int, a as int)
    ensures 
        valid_output(result) &&
        ((result@ == "Yes"@) <==> can_pay_exactly(n as int, a as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i32 for arithmetic operations instead of int */
    let n_i32 = n as i32;
    let a_i32 = a as i32;
    let remainder = n_i32 % 500;
    if remainder <= a_i32 {
        String::from("Yes")
    } else {
        String::from("No")
    }
}
// </vc-code>


}

fn main() {}