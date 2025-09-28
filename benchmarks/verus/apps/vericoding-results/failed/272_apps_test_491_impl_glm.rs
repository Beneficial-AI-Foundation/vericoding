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
/* helper modified by LLM (iteration 5): unchanged from previous iteration */
proof fn max_balance_in_range(n: int)
    requires valid_input(n) && -128 <= n <= 127
    ensures -128 <= max_balance_after_operation(n) <= 127
{
    if n >= 0 {
        assert(max_balance_after_operation(n) == n);
    } else {
        let option1 = n / 10;
        let option2 = (n / 100) * 10 + (n % 10);
        assert(-128 <= option1 <= 127);
        assert(-128 <= option2 <= 127);
        assert(-128 <= max_balance_after_operation(n) <= 127);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_balance_after_operation(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added assertions to help verifier prove postcondition */
{
    if n >= 0 {
        let result = n;
        assert(result as int == max_balance_after_operation(n as int));
        result
    } else {
        let option1 = n / 10;
        let quotient = n / 100;
        let remainder = n % 10;
        let option2 = quotient * 10 + remainder;
        let result = if option1 > option2 {
            option1
        } else {
            option2
        };
        assert(result as int == max_balance_after_operation(n as int));
        result
    }
}
// </vc-code>


}

fn main() {}