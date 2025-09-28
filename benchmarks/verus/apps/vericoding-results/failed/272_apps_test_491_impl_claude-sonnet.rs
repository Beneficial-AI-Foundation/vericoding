// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 10 || n <= -10
}

spec fn max_balance_after_operation(n: int) -> int
    recommends valid_input(n)
{
    if n >= 0 {
        n
    } else {
        /* For negative numbers, we need to delete either the last digit
           or the digit before the last digit to maximize the balance.
           Since this involves string operations that are not easily
           expressible in pure logic, we use a simplified specification. */
        let option1 = n / 10;
        let option2 = (n / 100) * 10 + (n % 10);
        if option1 > option2 { option1 } else { option2 }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added proof function to verify arithmetic operations */
proof fn verify_arithmetic_operations(n: i8)
    requires n < 0
    ensures (n / 10) as int == n as int / 10,
            ((n / 100) * 10 + (n % 10)) as int == (n as int / 100) * 10 + (n as int % 10)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_balance_after_operation(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added proof call and fixed comparison operator */
    if n >= 0 {
        n
    } else {
        proof {
            verify_arithmetic_operations(n);
        }
        let option1 = n / 10;
        let option2 = (n / 100) * 10 + (n % 10);
        if option1 > option2 { 
            option1 
        } else { 
            option2 
        }
    }
}
// </vc-code>


}

fn main() {}