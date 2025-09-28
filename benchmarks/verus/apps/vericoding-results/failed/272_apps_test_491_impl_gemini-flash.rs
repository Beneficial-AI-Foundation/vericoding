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
/* helper modified by LLM (iteration 5): This section now contains an empty implementation or only necessary helper functions. */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_balance_after_operation(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The postcondition failure indicates `int` to `i8` conversion may cause issues. Changed division behavior by making sure the negative values are handled correctly to ensure `max_balance_after_operation` matches implementation. */
{
    let n_i: i8 = n;

    if n_i >= 0 {
        n_i
    } else {
        let option1_val: i8 = n_i / 10;
        let option2_val: i8;

        // The `max_balance_after_operation` spec for negative numbers is implicitly using integer division
        // where -45 / 100 = 0 and -45 % 10 = -5.
        // We need to ensure that the i8 arithmetic matches this behavior exactly for the postcondition.

        let n_absolute = if n_i < 0 { -n_i } else { n_i };
        let hundred_val = n_absolute / 100;
        let ten_val = n_absolute % 10;

        if n_i / 100 == 0 && n_i / 10 != 0 { // For numbers like -10 to -99
           option2_val = (0 * 10) + (n_i % 10);
        } else { // For numbers like -100 to -127 or cases where n_i/100 is non-zero
             option2_val = (n_i / 100) * 10 + (n_i % 10);
        }

        if option1_val > option2_val {
            option1_val
        } else {
            option2_val
        }
    }
}
// </vc-code>


}

fn main() {}