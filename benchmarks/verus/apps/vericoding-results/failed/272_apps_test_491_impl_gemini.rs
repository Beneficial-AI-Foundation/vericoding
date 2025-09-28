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
/* helper modified by LLM (iteration 4): Fix compilation error by implementing Euclidean division with executable code */
fn euclid_div(a: i8, b: i8) -> (res: i8)
    requires b > 0
    ensures res as int == a as int / b as int
{
    let q = a / b;
    let r = a % b;
    if r < 0 {
        q - 1
    } else {
        q
    }
}

/* helper modified by LLM (iteration 4): Fix compilation error by implementing Euclidean modulus with executable code */
fn euclid_mod(a: i8, b: i8) -> (res: i8)
    requires b > 0
    ensures res as int == a as int % b as int
{
    let r = a % b;
    if r < 0 {
        r + b
    } else {
        r
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_balance_after_operation(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Re-using previous logic with corrected helper functions. */
    if n >= 0 {
        n
    } else {
        let option1 = euclid_div(n, 10);
        let option2 = euclid_div(n, 100) * 10 + euclid_mod(n, 10);

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