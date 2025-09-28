// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define spec function for sum formula */
spec fn sum_formula(n: u32) -> int {
    if n == 0 { 0 } else { (n as int) * ((n as int) + 1) / 2 }
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
{
    /* code modified by LLM (iteration 5): use u64 for intermediate calculations to avoid int in executable code */
    let sum = if n == 0 {
        0
    } else {
        let n64 = n as u64;
        let sum64 = (n64 * (n64 + 1)) / 2;
        sum64 as u32
    };
    let average_numerator = if n == 0 {
        0
    } else {
        sum * 10000 / n
    };
    (sum, average_numerator as f64 / 10000.0)
}
// </vc-code>

}
fn main() {}