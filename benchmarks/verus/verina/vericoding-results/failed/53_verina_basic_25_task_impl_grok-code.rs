// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added parentheses to while condition and invariant expressions for syntax compliance */
fn sum_to_n(n: u32) -> (result: u32)
    requires n > 0,
    ensures result == (n * (n + 1)) / 2,
{
    let mut sum = 0;
    let mut i = 1;
    while (i <= n)
        invariant (i <= n + 1)
        invariant (sum == ((i - 1) * i) / 2)
    {
        sum = sum + i;
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: u32) -> (result: (u32, f64))
    requires n < 100000,
    ensures
        n == 0 ==> result.0 == 0,
        n > 0 ==> result.0 == (n * (n + 1)) / 2,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Implementation utilizes the corrected helper function */
{
    if n == 0 {
        (0, 0.0)
    } else {
        let sum = sum_to_n(n);
        let average = (sum as f64) / (n as f64);
        (sum, average)
    }
}
// </vc-code>

}
fn main() {}